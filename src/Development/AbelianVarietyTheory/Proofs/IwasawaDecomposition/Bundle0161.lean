module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AutSpace

variable {D : D7} (θ : InfF D) (V : HSp D)

def SmFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)}
  add_mem' := fun ha hb k τs Xs h g => (ha k τs Xs h g).add (hb k τs Xs h g)
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  smul_mem' := fun c _ ha k τs Xs h g => (ha k τs Xs h g).const_smul c

variable {θ V}

theorem differentiable_oneP {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (g : GA D V) :
    Differentiable ℝ fun t : ℝ => φ (g * oneP θ V τ X t) := by
  have h := hφ 1 (fun _ => τ) (fun _ => X) (fun _ => hX) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem Rder_add {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (φ + ψ) = Rder θ V τ X φ + Rder θ V τ X ψ := by
  funext g
  exact deriv_fun_add (differentiable_oneP hφ hX g 0) (differentiable_oneP hψ hX g 0)

theorem Rder_smul (c : ℂ) (φ : GA D V → ℂ) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  exact deriv_const_mul_field c

theorem Rder_mem {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ SmFun θ V := by
  intro k τs Xs h g
  have h1 := hφ (k + 1) (Fin.snoc (α := fun _ => D.what₂.Tau) τs τ)
    (Fin.snoc (α := fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) Xs X)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hX
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * oneP θ V τ X s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))


variable (θ V) in
structure LinOnSm (T : (GA D V → ℂ) → (GA D V → ℂ)) : Prop where
  mem : ∀ φ ∈ SmFun θ V, T φ ∈ SmFun θ V
  add : ∀ φ ∈ SmFun θ V, ∀ ψ ∈ SmFun θ V, T (φ + ψ) = T φ + T ψ
  smul : ∀ (c : ℂ) φ, T (c • φ) = c • T φ

theorem linOnSm_Rder {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    LinOnSm θ V (Rder θ V τ X) :=
  ⟨fun _ h => Rder_mem h hX, fun _ h _ h' => Rder_add h h' hX, fun c φ => Rder_smul c φ τ X⟩

theorem linOnSm_RderC (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : LinOnSm θ V (RderC θ V τ Z) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨fun φ h => ?_, fun φ h ψ h' => ?_, fun c φ => ?_⟩
  · exact add_mem (Rder_mem h h1) (Submodule.smul_mem _ _ (Rder_mem h h2))
  · simp only [RderC]
    rw [Rder_add h h' h1, Rder_add h h' h2, smul_add Complex.I, add_add_add_comm]
  · simp only [RderC]
    rw [Rder_smul, Rder_smul, smul_add c, smul_comm c Complex.I]

theorem linOnSm_foldr {α : Type} (T : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (hl : ∀ a ∈ l, LinOnSm θ V (T a)) : LinOnSm θ V fun φ => l.foldr (fun a f => T a f) φ := by
  induction l with
  | nil => exact ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a l ih =>
    have h1 := hl a (by simp)
    have h2 := ih fun b hb => hl b (by simp [hb])
    refine ⟨fun φ h => h1.mem _ (h2.mem φ h), fun φ h ψ h' => ?_, fun c φ => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2.add φ h ψ h', h1.add _ (h2.mem φ h) _ (h2.mem ψ h')]
    · simp only [List.foldr_cons]
      rw [h2.smul, h1.smul]

theorem linOnSm_gelf (τ : D.what₂.Tau) (k : ℕ) : LinOnSm θ V (gelf θ V τ k) := by
  have h : ∀ idx : Fin (k + 1) → Fin V.rank, LinOnSm θ V fun φ =>
      (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
        (fun f acc => f acc) φ := fun idx =>
    linOnSm_foldr (fun f => f) _ fun f hf => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact linOnSm_RderC τ _
  refine ⟨fun φ hφ => Submodule.sum_mem _ fun idx _ => (h idx).mem φ hφ, fun φ hφ ψ hψ => ?_, fun c φ => ?_⟩
  · simp only [gelf]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun idx _ => (h idx).add φ hφ ψ hψ
  · simp only [gelf]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun idx _ => (h idx).smul c φ

theorem one_le_sum_norm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (i : Fin n) :
    1 ≤ ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) := by
  set S := ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) with hS
  have hS0 : 0 ≤ S := by positivity
  have hle : ∀ a b, ‖A a b‖ + ‖B a b‖ ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖A a b‖ + ‖B a b‖) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ a))
  have hrow : ∑ b, ‖A i b‖ ≤ S :=
    (Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (norm_nonneg (B i b))).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ i))
  have h1 : (1 : ℝ) ≤ S * S := by
    have e : (1 : ℂ) = ∑ b, A i b * B b i := by rw [← Matrix.mul_apply, h, Matrix.one_apply_eq]
    calc (1 : ℝ) = ‖∑ b, A i b * B b i‖ := by rw [← e, norm_one]
      _ ≤ ∑ b, ‖A i b‖ * S := (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg (A b i))).trans (hle b i))
            (norm_nonneg _))
      _ ≤ S * S := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hrow hS0
  nlinarith

variable (θ V) in
theorem infMat_mul_inv (τ : D.what₂.Tau) (g : GA D V) :
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  rw [e, e, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]


variable (θ V) in
theorem normInf_dichotomy : (∀ g, normInf θ V g = 0) ∨ ∀ g, 1 ≤ normInf θ V g := by
  by_cases h : Nonempty D.what₂.Tau ∧ Nonempty (Fin V.rank)
  · obtain ⟨⟨τ⟩, ⟨i⟩⟩ := h
    refine Or.inr fun g => (one_le_sum_norm _ _ (infMat_mul_inv θ V τ g) i).trans ?_
    exact Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
  · refine Or.inl fun g => Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun i _ => ?_
    exact (h ⟨⟨τ⟩, ⟨i⟩⟩).elim

variable (θ V) in
theorem exists_pow_ge (a b : ℕ) :
    ∃ N : ℕ, ∀ g, normInf θ V g ^ a ≤ normInf θ V g ^ N ∧ normInf θ V g ^ b ≤ normInf θ V g ^ N := by
  rcases normInf_dichotomy θ V with h | h
  · refine ⟨0, fun g => ?_⟩
    rw [h g, pow_zero]
    exact ⟨pow_le_one₀ le_rfl zero_le_one, pow_le_one₀ le_rfl zero_le_one⟩
  · exact ⟨max a b, fun g => ⟨pow_le_pow_right₀ (h g) (le_max_left _ _), pow_le_pow_right₀ (h g) (le_max_right _ _)⟩⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem isAutFunSm_smul (c : ℂ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.const_smul c⟩, (SmFun θ V).smul_mem c h.smooth, ?_, ?_⟩
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c h1, h2⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul c φ
    rw [this, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (θ V) in
theorem isAutFunSm_zero : IsAutFunSm θ V 0 := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, (SmFun θ V).zero_mem,
    ⟨⊥, inferInstance, zero_mem _, fun τ k f hf => ?_⟩, ⟨0, fun l hl x => ⟨0, fun g _ => ?_⟩⟩⟩
  · have := (linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 f
    rw [(Submodule.mem_bot ℂ).1 hf, zero_smul, zero_smul] at this
    rw [(Submodule.mem_bot ℂ).1 hf, this]
    exact zero_mem _
  · have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp

theorem isAutFunSm_add {φ ψ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (h' : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (φ + ψ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont⟩, (SmFun θ V).add_mem h.smooth h'.smooth, ?_, ?_⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    obtain ⟨W', hW', h1', h2'⟩ := h'.zfin
    refine ⟨(W ⊓ SmFun θ V) ⊔ (W' ⊓ SmFun θ V), inferInstance,
      Submodule.add_mem_sup ⟨h1, h.smooth⟩ ⟨h1', h'.smooth⟩, fun τ k f hf => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    have hg := linOnSm_gelf (θ := θ) (V := V) τ k
    rw [hg.add a ha.2 b hb.2]
    exact Submodule.add_mem_sup ⟨h2 τ k a ha.1, hg.mem a ha.2⟩ ⟨h2' τ k b hb.1, hg.mem b hb.2⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    obtain ⟨M, hM⟩ := exists_pow_ge θ V N N'
    refine ⟨M, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    obtain ⟨C', hC'⟩ := hN' l hl x
    refine ⟨|C| + |C'|, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).add φ h.smooth ψ h'.smooth
    rw [this, Pi.add_apply, add_mul]
    have h0 := normInf_nonneg (θ := θ) g
    refine (norm_add_le _ _).trans (add_le_add ((hC g hg).trans ?_) ((hC' g hg).trans ?_))
    · exact mul_le_mul (le_abs_self _) (hM g).1 (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (hM g).2 (pow_nonneg h0 _) (abs_nonneg _)

theorem mem_AFs_iff : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    φ ∈ AFs θ V ↔ IsAutFunSm θ V φ := by
  intro D θ _ V φ
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_zero θ V
  | add x y _ _ hx hy => exact isAutFunSm_add hx hy
  | smul c x _ hx => exact isAutFunSm_smul c hx

end GlobalTheory.Mem.AutSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineCoverSquarePolarisationSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquarePolCover.exists_cover : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type)
    (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  intro hA R _ _ P n hn
  obtain ⟨κ, t, ht, hta⟩ := GlobalTheory.Algebraise.exists_cover hA P (2 * n) (by omega)
  have hm : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
    intro X Y L a n m hm g s'
    have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
        LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
          LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
    refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
    · refine fn_ext fun y hy => ?_
      have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
      have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
      have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
      have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
      rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
      erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
      erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
        gs_res (𝟙 Y) y _ hy.2, c]
      erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
      have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
        simpa using Set.mem_iInter.1 hy.1 0
      have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
        simpa using Set.mem_iInter.1 hy.2 0
      simp only [Fin.prod_univ_one]
      erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
      simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
      rfl
    · intro Z r z j h
      exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm
  choose s hs using fun i => unflat P.L 2 n ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) (t i)
  have key : ∀ i, nonzeroLocus (s i) = nonzeroLocus (t i) := by
    intro i
    ext x
    obtain ⟨j, hj⟩ := exists_chart P.isLB x
    have h₁ := GlobalTheory.SectionRingIso.mem_iff_isUnit (t i) (𝟙 _) x (j := fun _ => j) hj
    have h₂ := GlobalTheory.SectionRingIso.mem_iff_isUnit (s i) (𝟙 _) x (j := fun _ => fun _ => j)
      (GlobalTheory.SectionRingIso.mem_ch.2 hj)
    have h₃ := hs i P.A.left (𝟙 _) x j hj
    exact h₂.trans ((congrArg IsUnit h₃).to_iff.symm.trans h₁.symm)
  refine ⟨κ, s, ?_, fun i => ?_⟩
  · simp_rw [key]; exact ht
  · rw [key]; exact hta i
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

section General

variable (F : Type) [Field F] [NumberField F]

def ratChar (x : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ))

theorem ratChar_add (x y : F) : ratChar F (x + y) = ratChar F x * ratChar F y := by
  rw [ratChar, ratChar, ratChar, ← Complex.exp_add, map_add (f := _)]
  congr 1
  push_cast
  ring

theorem ratChar_zero : ratChar F 0 = 1 := by simp [ratChar]

theorem norm_ratChar (x : F) : ‖ratChar F x‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (2 * Real.pi * ((Algebra.trace ℚ F x : ℚ) : ℝ))
  rw [← this, ratChar]
  congr 2
  push_cast
  ring

theorem ratChar_integer (r : 𝓞 F) : ratChar F (r : F) = 1 := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (r : F)) := Algebra.isIntegral_trace r.isIntegral_coe
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [ratChar, ← hk, eq_intCast, Rat.cast_intCast, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem ratChar_of_integral (x : F)
    (h : ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F) : ratChar F x = 1 := by
  have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
  rw [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
    FractionalIdeal.mem_one_iff] at hx
  obtain ⟨r, rfl⟩ := hx
  exact ratChar_integer F r

theorem exists_finChar : ∃ χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ, Continuous χ ∧ (∀ y, ‖χ y‖ = 1) ∧
    ∀ x : F, χ (algebraMap F _ x) = ratChar F x := by
  choose e s hs he using GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos
  simp only [one_smul] at he
  have key : ∀ (y : FiniteAdeleRing (𝓞 F) F) (a : F) (w : FiniteAdeleRing (𝓞 F) F),
      (∀ v, w v ∈ v.adicCompletionIntegers F) → y = algebraMap F _ a + w → ratChar F (e y) = ratChar F a := by
    intro y a w hw h
    have h2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (e y - a) = w - s y := by
      rw [map_sub]
      linear_combination h - he y
    have h3 := ratChar_of_integral F (e y - a) fun v => by
      rw [h2]; exact sub_mem (hw v) (hs y v)
    rw [show e y = a + (e y - a) by ring, ratChar_add, h3, mul_one]
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    { toFun := fun y => ratChar F (e y)
      map_zero_eq_one' := (key 0 0 0 (fun v => zero_mem _) (by simp)).trans (ratChar_zero F)
      map_add_eq_mul' := fun x y => by
        rw [← ratChar_add]
        refine key _ _ (s x + s y) (fun v => add_mem (hs x v) (hs y v)) ?_
        rw [map_add (f := _)]
        linear_combination he x + he y }
  refine ⟨χ, ?_, fun y => norm_ratChar F _, fun x => key _ x 0 (fun v => zero_mem _) (add_zero _).symm⟩
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hc : Continuous fun z : FiniteAdeleRing (𝓞 F) F => z - y := continuous_id.sub continuous_const
  have hU := ((GlobalTheory.AdLat.OpenLat.isOpen_integral F).preimage hc).mem_nhds (x := y) (by
    intro v
    simp only [sub_self]
    exact zero_mem _)
  refine (continuousAt_const (y := χ y)).congr (Filter.mem_of_superset hU fun z hz => ?_)
  refine (key z (e y) (s y + (z - y)) (fun v => add_mem (hs y v) (hz v)) ?_).symm
  linear_combination he y

theorem exists_char_of_trace (L : Ainf F →+ ℂ) (hL : Continuous L)
    (hT : ∀ x : F, L (algebraMap F _ x) = ((Algebra.trace ℚ F x : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := by
  obtain ⟨χ, hc, hn, hr⟩ := exists_finChar F
  have him : ∀ x, (L x).im = 0 := by
    have : (fun x => (L x).im) = fun _ => (0 : ℝ) := by
      refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer (Complex.continuous_im.comp hL)
        continuous_const ?_
      funext x
      show (L (algebraMap F _ x)).im = 0
      rw [hT, Complex.ratCast_im]
    exact congrFun this
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun a => Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, Complex.exp_add, AddChar.map_add_eq_mul]
        ring }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) := fun x => by
    show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L x) * χ 0 = _
    rw [AddChar.map_zero_eq_one, mul_one]
  refine ⟨ψ, ⟨?_, fun a => ?_, fun a => ?_, ?_⟩, hinf⟩
  · exact (Complex.continuous_exp.comp (continuous_const.mul (hL.comp continuous_fst))).mul
      (hc.comp continuous_snd)
  · show ‖Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F a)) * χ (sndA F a)‖ = 1
    rw [norm_mul, hn, mul_one, Complex.norm_exp]
    simp [him]
  · show Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * L (fstA F (algebraMap F _ a))) *
      χ (sndA F (algebraMap F _ a)) = 1
    rw [AlgHom.commutes, AlgHom.commutes, hT, hr, ratChar, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  · have hd : ((Module.finrank ℚ F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ)))) 0, ?_⟩
    have h := hinf (algebraMap F _ (algebraMap ℚ F (-(1 / 2) / (Module.finrank ℚ F : ℚ))))
    rw [hT, Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_cancel₀ _ hd, psiInf] at h
    have e : 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ((-(1 / 2) : ℚ) : ℂ) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [h, e, Complex.exp_pi_mul_I]
    norm_num

end General

theorem exists_isStdChar : ∀ D : D7, ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let L : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  obtain ⟨ψ, h1, h2⟩ := exists_char_of_trace D.host.F L (continuous_finsetSum _ fun ρ _ => (hθ ρ).2) fun x => by
    show ∑ ρ, θ ρ (algebraMap D.host.F (Ainf D.host.F) x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace]
  refine ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => ?_⟩
  rw [h2, GlobalTheory.DualPairCompare.sum_infFam θ' hθ', ← GlobalTheory.DualPairCompare.sum_infFam θ hθ]
  rfl

end GlobalTheory.StdAdelicChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheafStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData),
    IsProjOver s → ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ GlobalTheory.ProjBlowup.Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates_isLB | exact GlobalTheory.ProjBlowup.exists_generates_isLB | (intros; apply GlobalTheory.ProjBlowup.exists_generates_isLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentsAdelicUnitaryElementStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_components_adelic_unitary_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (B : Matrix (Fin (M + 1)) (Fin M) E) (g : HA (AF F) σ J), ∃ (gi : HA (Ainf F) σ J) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), projInf (g • ratTup (F := F) (AF F) x) = gi • ratTup (F := F) (Ainf F) x ∧ (∀ v, projV v (projFin (g • ratTup (F := F) (AF F) x)) = gv v • ratTup (F := F) (Fv F v) x) ∧ (∀ y y', projInf (pairOf (AF F) σ J B y g y') = pairOf (Ainf F) σ J B (projInf y) gi (projInf y')) ∧ (∀ v y y', projV v (projFin (pairOf (AF F) σ J B y g y')) = pairOf (Fv F v) σ J B (projV v (projFin y)) (gv v) (projV v (projFin y'))) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, (HA.mat (Fv F v) σ J (gv v)).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J ((gv v))⁻¹).val i j ∈ intV b v := by
  first | exact @GlobalTheory.GaugeEx.LocComp.exists_local_components | exact GlobalTheory.GaugeEx.LocComp.exists_local_components | (intros; apply GlobalTheory.GaugeEx.LocComp.exists_local_components <;> assumption)
end

