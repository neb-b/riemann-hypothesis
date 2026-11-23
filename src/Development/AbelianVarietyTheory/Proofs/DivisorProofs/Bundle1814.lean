module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilSchUnique

variable {F : Type} [Field F] [NumberField F]


open scoped Classical in
theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem scalar_of_commute (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (ha : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (hc : ∀ w, ∀ φ ∈ schA F κ, T (schr ψ w φ) = schr ψ w (T φ)) :
    ∃ c : ℂ, ∀ φ ∈ schA F κ, T φ = c • φ := by
  obtain ⟨c, hc'⟩ := _root_.GlobalTheory.CharInvForm.main F ψ hψ κ (LinearMap.proj 0 ∘ₗ T) (ha _ (evalZero_mem_adelicSchwartzAdmittedForms κ)) (fun y φ hφ => by
    have e : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    rw [e, hc _ φ hφ]; simp [schr])
  refine ⟨c, fun φ hφ => funext fun x => ?_⟩
  have h1 := congrFun (hc (x, 0) φ hφ) 0
  have e : schr ψ (x, 0) φ = fun z => φ (z + x) := by funext z; simp [schr]
  have h2 := hc' _ (e ▸ _root_.GlobalTheory.SchwartzTranslate.main F κ x φ hφ)
  simp only [LinearMap.comp_apply, LinearMap.proj_apply] at h2
  rw [h1] at h2
  simp [schr] at h2
  simpa [e] using h2

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

theorem dd_rho_diag {a b : ℕ} {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ}
    {dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (κ ⊕ κ)}
    (h : IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem member_unique (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) {κ : Type} [Fintype κ]
    (d : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (χ : Chr F E)
    (om om₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ om)
    (h₁ : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ om₁) :
    ∀ g, ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  have hee : ∀ w, dd₁.e w = dd.e w := fun w => by
    rw [← Matrix.fromCols_toCols w, hdd, hdd₁]
  have hrho : ∀ w, dd₁.rho ψ w = dd.rho ψ w := fun w => by simp only [Darboux.rho, hee]
  have inv_mul : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (κ ⊕ κ)

  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ)) = omd p⁻¹ (omd₁ p (dd₁.rho ψ w' φ)) := by rw [hrho]
          _ = omd p⁻¹ (dd₁.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = omd p⁻¹ (dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hrho]
          _ = dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this

  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := _root_.GlobalTheory.diagLagrangian_form F ψ κ
  have hP : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (t : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      ((p : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) p t hpt _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) p t hpt _ hφ
    rw [← e2, hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := _root_.GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (Fin b) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) g
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  have hb := _root_.GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1 gd, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

theorem weil_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → ∀ om om₁ : Rep σ X W, M.IsWeil ψ χX χW om → M.IsWeil ψ χX χW om₁ → ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ = om₁ x Φ := by
  intro F E _ _ _ _ _ σ hσ n d X W M ψ χX χW hψ hX hXd hW hWd om om₁ h h₁ x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_unique σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_unique σ hσ W.J X.J 1 eX hXd ψ hψ _ χW _ _ hA hA₁
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, x.2) Φ = om₁ (1, x.2) Φ := uB x.2 Φ hΦ
  rw [h1]
  exact uA x.1 _ (hB₁.1.pres x.2 Φ hΦ)

end GlobalTheory.WeilSchUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImage
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.LevelLatticeCong

theorem cong_add {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ)
    {u₁ u₂ y₁ y₂ : Fin n → R} (f₁ : t • (K *ᵥ u₁ - u₁) = M • y₁) (f₂ : t • (K *ᵥ u₂ - u₂) = M • y₂) :
    t • (K *ᵥ (u₁ + u₂) - (u₁ + u₂)) = M • (y₁ + y₂) := by
  rw [smul_add, ← f₁, ← f₂, Matrix.mulVec_add, ← smul_add]
  congr 1
  abel

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t s : R) (M : ℕ)
    {u w : Fin n → R} (f : t • (K *ᵥ u - u) = M • w) :
    t • (K *ᵥ (s • u) - s • u) = M • (s • w) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, f, smul_comm]

end GlobalTheory.LevelLatticeCong

namespace GlobalTheory.LevelLatticeCong

theorem cong_on_sdLattice : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  intro D V β Λ hβ La _ _ ι hι K t M h
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [← GlobalTheory.OneMapRef.Lift.hatV_eq hβ]; rfl

  have hfv : ∀ (e : D.host.E) (v : Fin V.rank → D.host.E),
      finVec V (e • v) = ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] e) • finVec V v := by
    intro e v; funext i
    simp only [finVec, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hint : ∀ c : 𝓞 D.host.E, ∀ z ∈ latHat V,
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latHat V := by
    intro c z hz
    rw [hl] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int Λ c hz

  have hinv : ∀ b ∈ ((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      ∀ w ∈ latGHat V 1, ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w ∈ latHat V := by
    intro b hb
    let s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
      (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b
    let H : AddSubgroup (Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
      (latHat V).comap (DistribSMul.toAddMonoidHom _ s)
    suffices hle : latGHat V 1 ≤ H from fun w hw => hle hw
    rw [GlobalTheory.LevelActionPinned.latGHat_one, AddSubgroup.closure_le]
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
        exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hba
      have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) •
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) • z) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z := by
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 2
        exact hc.symm
      show s • _ ∈ latHat V
      rw [e]; exact hint c z hz
  let P : D.host.E → Prop := fun e => ∀ x ∈ Λ, ∃ y ∈ latHat V,
    t • (K *ᵥ finVec V (e • x) - finVec V (e • x)) = M • y
  have hadd : ∀ e₁ e₂ : D.host.E, P e₁ → P e₂ → P (e₁ + e₂) := by
    intro e₁ e₂ h₁ h₂ x hx
    obtain ⟨y₁, hy₁, f₁⟩ := h₁ x hx
    obtain ⟨y₂, hy₂, f₂⟩ := h₂ x hx
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    have e0 : finVec V ((e₁ + e₂) • x) = finVec V (e₁ • x) + finVec V (e₂ • x) := by
      rw [add_smul]; funext i; exact TensorProduct.tmul_add _ _ _
    rw [e0]
    exact cong_add K t M f₁ f₂
  have hmul : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      ∀ b ∈ (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E), P (a * b) := by
    intro a ha b hb x hx
    have hxL : finVec V x ∈ latHat V := by
      rw [hl]; exact GlobalTheory.Member.AALev.fv_mem_hat _ hx
    have hax : a • x ∈ latG V 1 := by
      refine Submodule.subset_span ⟨a, ha, x, ?_, rfl⟩
      refine ⟨finVec V x, hxL, ?_⟩
      simp only [map_one, Units.val_one, Matrix.one_mulVec]
    rw [← hι.2] at hax
    obtain ⟨a', ha'⟩ := hax
    obtain ⟨w, hw, e⟩ := h a'
    rw [ha'] at e
    refine ⟨((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w, hinv b hb w hw, ?_⟩
    have e1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    rw [e1, hfv b]
    exact cong_smul K t _ M e
  have h1 : (1 : D.host.E) ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have hP : P 1 := Submodule.mul_induction_on h1 hmul hadd
  intro x hx
  simpa only [one_smul] using hP x hx

end GlobalTheory.LevelLatticeCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModelStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coords_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
        Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  first | exact @GlobalTheory.SympChangeBij.change_of_coordinates_bij | exact GlobalTheory.SympChangeBij.change_of_coordinates_bij | (intros; apply GlobalTheory.SympChangeBij.change_of_coordinates_bij <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSp
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma vecMulVec_mul_transpose' {m k : Type} [Fintype k] {R : Type} [CommRing R] (p : m → R) (q : k → R)
    (M : Matrix k k R) : Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d ⊕ Fin d → AE F E} (hq : q ∈ GlobalTheory.DblVac.latD W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latDbl X W v := by
  refine ⟨?_, ?_⟩
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₁ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inl) := by
      ext i j; simp [Matrix.toCols₁, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.1
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₂ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inr) := by
      ext i j; simp [Matrix.toCols₂, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.2

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hM : ∀ q ∈ GlobalTheory.DblVac.latD W v, M *ᵥ q ∈ GlobalTheory.DblVac.latD W v) :
    ∀ γ ∈ latDbl X W v, γ * Mᵀ ∈ latDbl X W v := by

  let φ₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols γ 0 : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  let φ₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols 0 γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  have key : ∀ (φ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)),
      (∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ x ∈ X.L, ∀ y ∈ W.L,
        ∃ q ∈ GlobalTheory.DblVac.latD W v,
          φ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) →
      latAtV X W v ≤ (latDbl X W v).comap φ := by
    intro φ hφ
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    obtain ⟨q, hq, he⟩ := hφ a ha hai x hx y hy
    show φ _ ∈ latDbl X W v
    rw [he]; exact vecMulVec_mem_latDbl X W v hx hq
  have gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun a ha hai y hy =>
    AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
  have h₁ : latAtV X W v ≤ (latDbl X W v).comap φ₁ := by
    refine key φ₁ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim (a • fun i => inclR (F := F) (AF F) (y i)) 0, hM _ ?_, ?_⟩
    · exact ⟨by simpa using gen a ha hai y hy, by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₁, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  have h₂ : latAtV X W v ≤ (latDbl X W v).comap φ₂ := by
    refine key φ₂ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (y i)), hM _ ?_, ?_⟩
    · exact ⟨by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem, by simpa using gen a ha hai y hy⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₂, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  intro γ hγ
  have hsplit : γ * Mᵀ = φ₁ γ.toCols₁ + φ₂ γ.toCols₂ := by
    simp only [φ₁, φ₂, AddMonoidHom.mk'_apply]
    rw [← Matrix.add_mul]
    congr 1
    ext i (j | j) <;> simp [Matrix.toCols₁, Matrix.toCols₂]
  rw [hsplit]
  exact (latDbl X W v).add_mem (h₁ hγ.1) (h₂ hγ.2)

end GlobalTheory.DblVacStab

theorem GlobalTheory.DblVac.kD_stab_latDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  intro F E _ _ _ _ _ σ n d X W v g hg γ hγ
  exact ⟨GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).1) γ hγ,
    GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).2) γ hγ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionIntertwinesGroupAction
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_rowAct (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι)
    (A : ι → Matrix (Fin N) (Fin N) (O ⧸ Ideal.span {ϖ})) (M : Matrix (Fin N) (Fin N) O)
    (hA : A τ = M.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (rowAct O M f) = blockSub (O ⧸ Ideal.span {ϖ}) N A (blockRed O N ϖ τ f) := by
  have h : (blockRed O N ϖ τ).comp (rowAct O M) =
      ((blockSub (O ⧸ Ideal.span {ϖ}) N A).restrictScalars O).comp (blockRed O N ϖ τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, rowAct, blockRed, blockSub, aeval_X, map_sum, map_mul,
      hA, Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [aeval_C]
    rfl
  exact congrArg (fun φ => φ f) h

end GlobalTheory.HighWtEmb

theorem GlobalTheory.HighWtEmb.redT_grp : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (g : ι → GL (Fin N) O) (y : NablaT O N mu), redT O N mu ϖ (grp O N mu g y) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ g y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    have h1 := (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nabla_rep_tensor_product O ι (fun _ => N) (fun _ => N) (fun τ => res N (mu τ)) g m)
    simp only [GlobalTheory.ExpFrame.grp]
    rw [h1.1]
    simp only [redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_prod, IsScalarTower.algebraMap_apply O (O ⧸ Ideal.span {ϖ}), AlgHom.commutes]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [h1.2 τ]
    exact blockRed_rowAct O N ϖ τ _ _ rfl _
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end
end

