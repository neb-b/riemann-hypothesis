module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLagUniq

open GlobalTheory.LatVac GlobalTheory.InertVacLag

theorem finrank_le_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank K Λ ≤ Fintype.card κ := by
  classical
  let B : LinearMap.BilinForm K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hB : ∀ a b, B a b = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun _ _ => rfl
  have hker : LinearMap.ker B = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' : ∀ b, B a b = 0 := fun b => by rw [LinearMap.mem_ker.1 ha]; rfl
    refine (Submodule.mem_bot _).2 (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
    · have := ha' (0, Pi.single k 1)
      simpa [hB] using this
    · have := ha' (Pi.single k 1, 0)
      simpa [hB] using this
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) Λ
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Λ ≤ B.orthogonal Λ := fun b hb a ha => by
    show B a b = 0
    rw [hB, h a ha b hb, sub_self]
  have h3 := Submodule.finrank_mono h2
  omega

theorem finrank_eq_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ Λ' : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank K Λ = Fintype.card κ := by
  have h1 := finrank_le_of_isotropic Λ h
  have h2 := finrank_le_of_isotropic Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (h : PsiUnr ψ v) : Continuous (psiAt ψ v) := by
  have hker : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    have := (h 1).2 (one_mem _) y hy
    rwa [one_mul] at this
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
  rw [AddChar.map_add_eq_mul, hker s hs, mul_one]

theorem psiAt_ne_one (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (h : PsiUnr ψ v) : psiAt ψ v ≠ 1 := by
  intro h1
  have hall : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F := fun x => (h x).1 fun y _ => by
    rw [← psiAt_apply, h1]; rfl
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h2 := hall (algebraMap F (Fv F v) π⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  rw [map_inv₀, map_inv₀, Algebra.algebraMap_self_apply, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

theorem liftV_one_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl (F := F)) (u : M) (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem liftV_one_mul (v : Pl (F := F)) (x : AF F) : liftV v (1 : Fv F v) * x = liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := liftV_one_smul v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

theorem liftV_one_smul_eq_zero (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ha : compFin F E v a = 0) : liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), liftV v (1 : Fv F v) • a = (liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  rw [key, ha, map_zero]

theorem exists_map_compFin (v : Pl (F := F)) {α β : Type} (A : Matrix α β (Fv F v ⊗[F] E)) :
    ∃ C : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = A := by
  refine ⟨A.map ((liftV v).rTensor E), ?_⟩
  ext i j
  simp only [Matrix.map_apply]
  induction A i j using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem mul_eq_self {n d : ℕ} (v : Pl (F := F)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hu : At (evFin F v) u)
    (N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hN : N.map (compFin F E v) = 1) : u * N = u := by
  have h0 : liftV v (1 : Fv F v) • (N - 1) = 0 := by
    ext i j
    refine liftV_one_smul_eq_zero v _ ?_
    have := congrFun (congrFun hN i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : u * (N - 1) = 0 := by
    rw [← liftV_one_smul v u hu, Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h1

theorem at_mul {α β γ : Type} [Fintype β] (v : Pl (F := F)) (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hu : At (evFin F v) u)
    (A : Matrix β γ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evFin F v) (u * A) := fun t ht => by
  rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

theorem exists_compl (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) (n : ℕ) : ∃ C' : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsLagrAt σ W v C' ∧
      ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → ∃ x ∈ lagAt v C, ∃ y ∈ lagAt v C', u = x + y := by
  obtain ⟨h0, Cx, M, hx, h1, h2⟩ := hC
  obtain ⟨C', hC'⟩ := exists_map_compFin v Cx
  obtain ⟨M₁, hM₁⟩ := exists_map_compFin v M.toRows₁
  obtain ⟨M₂, hM₂⟩ := exists_map_compFin v M.toRows₂
  rw [← Matrix.fromRows_toRows M] at h1 h2
  rw [Matrix.fromCols_mul_fromRows] at h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  refine ⟨C', ⟨by rw [hC']; exact hx, _, Matrix.fromRows M.toRows₂ M.toRows₁, h0, ?_, ?_⟩, fun u hu => ?_⟩
  · rw [hC', Matrix.fromCols_mul_fromRows, add_comm, h1]
  · rw [hC', Matrix.fromRows_mul_fromCols, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, Matrix.fromBlocks_one]
  · have hN : ((C * M₁ + C' * M₂)ᵀ).map (compFin F E v) = 1 := by
      rw [Matrix.transpose_map, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hC', hM₁, hM₂, h1,
        Matrix.transpose_one]
    refine ⟨u * M₁ᵀ * Cᵀ, ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, u * M₂ᵀ * C'ᵀ,
      ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, mul_eq_self v u hu _ hN]

theorem exists_at_locCo {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl (F := F)) (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ locCo co v u = p := by
  refine ⟨co.e.symm (fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun k => at_liftV v (p.1 k) r hr) (funext fun k => at_liftV v (p.2 k) r hr)
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => evFin_liftV v _) (funext fun k => evFin_liftV v _)

variable {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def lagCo (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := locCo M.co v '' lagAt v C
  zero_mem' := ⟨0, ⟨fun u _ => smul_zero u, 0, by simp⟩, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩ ⟨_, ⟨hy, z', rfl⟩, rfl⟩
    exact ⟨_, ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩, map_add _ _ _⟩
  smul_mem' := by
    rintro a _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩
    refine ⟨liftV v a • (z * Cᵀ), ⟨fun u hu => by rw [smul_comm, hx u hu, smul_zero], liftV v a • z,
      by rw [Matrix.smul_mul]⟩, ?_⟩
    ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul]

theorem lagCo_isotropic (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) : ∀ a ∈ lagCo M v C, ∀ b ∈ lagCo M v C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
  have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ X.J W v C hC (-1) u u' hu hu'
  change symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u' = 0 at h0
  rw [M.co.form] at h0
  have h1 := congrArg (evFin F v) h0
  rw [← sub_eq_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

theorem finrank_lagCo (M : Model σ X W) (v : Pl (F := F)) {m : ℕ} (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hC : IsLagrAt σ W v C) : Module.finrank (Fv F v) (lagCo M v C) = Fintype.card (Fin n × Fin d) := by
  obtain ⟨C', hC', hdec⟩ := exists_compl σ W v C hC n
  refine finrank_eq_of_isotropic _ (lagCo M v C') (lagCo_isotropic M v C hC) (lagCo_isotropic M v C' hC') ?_
  rw [eq_top_iff]
  intro p _
  obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co v p
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec u hu
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

theorem exists_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ v hψ m C hC
  have hc := continuous_psiAt ψ v hψ
  have hinv : ∀ l, HeisInv M ψ v C l → ∀ w ∈ lagCo M v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l (schr (psiAt ψ v) w φ) = l φ := by
    rintro l hl _ ⟨u, hu, rfl⟩ φ hφ
    exact hl u hu φ hφ _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ hc _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu.1 φ)
  by_cases hex : ∃ l₂, HeisInv M ψ v C l₂ ∧ ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l₂ φ ≠ 0
  · obtain ⟨l₂, hl₂, φ₀, hφ₀, hne⟩ := hex
    refine ⟨φ₀, hφ₀, fun l hl h0 φ hφ => ?_⟩
    obtain ⟨c, hcl⟩ := GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace F v (psiAt ψ v) hc (psiAt_ne_one ψ v hψ) _ (lagCo M v C) (lagCo_isotropic M v C hC)
      (finrank_lagCo M v C hC) l l₂ (hinv l hl) (hinv l₂ hl₂) ⟨φ₀, hφ₀, hne⟩
    have hc0 : c = 0 := (mul_eq_zero.1 ((hcl φ₀ hφ₀).symm.trans h0)).resolve_right hne
    rw [hcl φ hφ, hc0, zero_mul]
  · refine ⟨0, zero_mem _, fun l hl _ φ hφ => ?_⟩
    by_contra hne
    exact hex ⟨l, hl, φ, hφ, hne⟩

end GlobalTheory.InertLagUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.GramFrame

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x u v : n → A) : Formalism.UG.hform τ J x (u + v) = Formalism.UG.hform τ J x u + Formalism.UG.hform τ J x v := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (x y : n → A) : Formalism.UG.hform τ J x (a • y) = a * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x : n → A) : Formalism.UG.hform τ J x 0 = 0 := by
  simp [Formalism.UG.hform]

variable {D : D7}

theorem sigR_inclE (x : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (D.sp.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem inclE_int (b : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (algebraMap (𝓞 D.host.E) D.host.E b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)

theorem hform_inclE {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) =
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, sigR_inclE, Matrix.map_apply]
  rfl

theorem pair_hatL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (x y : Fin n → Formalism.IndefR.Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) x y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y0, hy0, rfl⟩ := hy
      rw [hform_inclE]
      obtain ⟨b, hb⟩ := h x0 hx0 y0 hy0
      rw [← hb]
      exact inclE_int b
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [hform_add_right]; exact add_mem ha hb
    | smul s a _ ha => rw [Subring.smul_def, hform_smul_right]; exact mul_mem s.2 ha
  | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
  | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
    exact mul_mem (GlobalTheory.LevSplit.sigR_int s.2) ha

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_hform' {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    Formalism.UG.prV (E := E) v (Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x y) =
    Formalism.UG.hform (Formalism.UG.sigR σ (v.adicCompletion F))
      (J.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)))
      (fun i => Formalism.UG.prV (E := E) v (x i)) (fun i => Formalism.UG.prV (E := E) v (y i)) := by
  have hs : ∀ z, Formalism.UG.prV (E := E) v (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) z) =
      Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.prV (E := E) v z) :=
    fun z => RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hs, Matrix.map_apply]
  rfl

theorem inv_int {n : ℕ} (σ : E →ₐ[F] E)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E)
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hlat : Submodule.IsFullLattice E Λ) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (hd : Formalism.L2.Forms.dualL (σ : E →+* E) J Λ ≤ Λ)
    (G' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hG' : Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
      J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.val * G' = 1) :
    ∀ i j, G' i j ∈ Formalism.L2.Herm.intAf F E := by
  intro i j
  have key : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x
        (β.val *ᵥ (G' *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.intAf F E := by
    intro x hx
    have ha := (hfr x).1 hx
    have e : x = β.val *ᵥ ((β⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, GlobalTheory.DualCompletion.hform_mulVec_left]
    have e2 : (Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
        J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ (β.val *ᵥ (G' *ᵥ Pi.single j 1)) =
        Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
    rw [e2]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hσ _ (ha k)) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k)) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
            (v.adicCompletionIntegers F).toSubring) Λ := by
    intro v
    have hm := (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v Λ hlat
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k))).2
    refine Submodule.span_mono (Set.image_mono hd) (hm fun u hu => ?_)
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x0, hx0, rfl⟩ := hu
      have h3 := key _ (Submodule.subset_span ⟨x0, hx0, rfl⟩)
      have h4 := Formalism.UG.P.afsplit_prV_int (E := E) v _ h3
      rw [prV_hform'] at h4
      exact h4
    | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
    | smul s a _ ha =>
      rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
      exact mul_mem (Formalism.L2.G.RelativeIndexFlags.sigR_mem v σ s.2) ha
  have hc : β.val *ᵥ (G' *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    Formalism.L2.Geo.Def.PN.latS_of_loc Λ hlat.span_eq_top _ hloc
  have h5 := (hfr _).1 hc i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_single_one] at h5
  exact h5

end General

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_entry {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (Formalism.UG.cT τ B * J * B) i j = Formalism.UG.hform τ J (B *ᵥ Pi.single i 1) (B *ᵥ Pi.single j 1) := by
  rw [GlobalTheory.DualCompletion.hform_col, map_one, one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

end GlobalTheory.GramFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestExtra
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.GramDet

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  set A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm with hA'
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [hA', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  intro h0
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem det_ne_zero_of_map {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) {J : Matrix (Fin n) (Fin n) K}
    (h : (J.map φ).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨det_ne_zero_of_map (B.emb w).1 (det_ne_zero_of_hasSig (hT.geo.hV'.sig w)), ?_⟩
  refine det_ne_zero_of_map (B.emb w).1 ?_
  have h := det_ne_zero_of_hasSig (hT.geo.hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  exact h (by rw [h0, mul_zero])

end GlobalTheory.GramDet
end

