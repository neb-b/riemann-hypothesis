module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.FinPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl F) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobal.opFin G om v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobal.FinPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.FinPlaceSmall

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V' hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om' (1, h)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobalPair.opFin om' v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobalPair.FinPlaceSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorFinal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLineTransp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField F] [NumberField E] in
theorem symp_transpose {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] (c : K →ₐ[R] K)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : K) (JA : Matrix α α K) (JB : Matrix β β K)
    (x y : Matrix α β K) : symp (R := R) c ξ JB JA xᵀ yᵀ = symp (R := R) c ξ JA JB x y := by
  unfold symp hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] in
theorem at_transpose {m n : Type} (v : Pl (F := F)) (z : Matrix m n (AE F E)) :
    At (evFin F v) zᵀ ↔ At (evFin F v) z := by
  constructor
  · intro h u hu
    have := h u hu
    rw [← Matrix.transpose_smul] at this
    simpa using congrArg Matrix.transpose this
  · intro h u hu
    rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

theorem transpose_mem_latAtV {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d) (AE F E)}
    (hz : z ∈ latAtV X Y v) : zᵀ ∈ latAtV Y X v := by
  have hle : latAtV X Y v ≤ (latAtV Y X v).comap (Matrix.transposeAddEquiv (Fin n) (Fin d) (AE F E)).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    show (a • incM F (Matrix.vecMulVec x y))ᵀ = _
    simp only [incM, Matrix.transpose_smul, ← Matrix.transpose_map, Matrix.transpose_vecMulVec]
  exact hle hz

theorem mem_latAtV_transpose {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (AE F E)) :
    zᵀ ∈ latAtV Y X v ↔ z ∈ latAtV X Y v :=
  ⟨fun h => by simpa using transpose_mem_latAtV Y X v h, transpose_mem_latAtV X Y v⟩


open GlobalTheory.DblVacLine in
theorem dbl_line_co {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hunr : PsiUnr ψ v) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J)) κ) (φ : (κ → Fv F v) → ℂ)
    (hφ : φ ∈ SB _ ∧ φ ≠ 0 ∧ ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 ∧ ∀ γ ∈ latAtV X Y v, Acts (evFin F v) (co.rho ψ γ) φ
      (ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) γ γ) • φ))
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J))) (κ ⊕ κ))
    (omd : UG (cA σ) (dbl (incM F Y.J)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F Y.J) co dd)
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (R : (κ → AF F) → ℂ) (hR : Rest (evFin F v) φ R)
    (g : GlobalTheory.InertDbl.UD σ Y) (hg : g ∈ GlobalTheory.InertDbl.KAtD σ Y v) :
    ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R)) = c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) := by
  classical
  by_cases hR0 : R = 0
  · have e : GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) = 0 := by
      funext x; simp [hR0, GlobalTheory.InertDbl.dblFun, boxFun, tens]
    exact ⟨0, by rw [e, map_zero, smul_zero]⟩
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hR0
  obtain ⟨hφSB, hφ0, θ, -, hvac⟩ := hφ
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  set Λ := latAtV X Y v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1
  set φd := boxFun φ fun x => star (φ x) with hφd
  set Rd := GlobalTheory.InertDbl.dblFun R with hRd
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) with hΦ
  have hΦt : Φ = tens (evFin F v) φd Rd := dblFun_tens v φ R
  have hrest : Rest (evFin F v) φd Rd := rest_dbl v hR
  have hΦs : Φ ∈ schA F _ := hΦt ▸ hrest.2
  have hRd0 : Rd (Sum.elim x₀ x₀) ≠ 0 := by
    show R x₀ * star (R x₀) ≠ 0
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)
  have hφdSB : φd ∈ SB _ := box_mem_SB hφSB ⟨hφSB.1.comp star, hφSB.2.comp_left (star_zero ℂ)⟩
  let cf : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → ℂ := fun w =>
    ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J)) w w)

  have h1 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, dd.rho ψ (Matrix.fromCols γ₁ γ₂) Φ = cf (Matrix.fromCols γ₁ γ₂) • Φ := by
    intro γ₁ h₁ γ₂ h₂
    have e₁ := hvac γ₁ h₁ R hR
    have e₂ := hvac γ₂ h₂ R hR
    rw [GlobalTheory.VacTransport.tens_smul] at e₁ e₂
    simp only [Darboux.rho] at e₁ e₂
    rw [Darboux.rho, hdd, hΦ, GlobalTheory.InertDbl.dblFun, schr_box ψ hn, e₁, e₂]
    funext x
    simp only [cf, symp_dbl, boxFun, Pi.smul_apply, smul_eq_mul, star_mul', star_eq_neg ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring

  have h2 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (omd g Φ) = cf (Matrix.fromCols γ₁ γ₂) • omd g Φ := by
    intro γ₁ h₁ γ₂ h₂
    obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := fromCols_mul_transpose X Y v (GlobalTheory.InertDbl.matD g⁻¹) (fun z hz => (hg.2 z hz).2) h₁ h₂
    have hback : actB (cA σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols γ₁ γ₂ := by
      change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
      have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
      rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
    have hsy : cf (Matrix.fromCols δ₁ δ₂) = cf (Matrix.fromCols γ₁ γ₂) := by
      simp only [cf]
      rw [← he, GlobalTheory.VacTransport.symp_mul_transpose (cA σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2]
    have h := hS.impl g (Matrix.fromCols δ₁ δ₂) Φ hΦs
    rw [hback, h1 δ₁ k₁ δ₂ k₂, map_smul, hsy] at h
    exact h.symm

  obtain ⟨φ₁, -, hact⟩ := acts_of_at hψ dd omd hS v g hg.1 φd hφdSB
  have hT : omd g Φ = tens (evFin F v) φ₁ Rd := by rw [hΦt]; exact hact Rd hrest
  have hrest₁ : Rest (evFin F v) φ₁ Rd := ⟨hrest.1, hT ▸ hS.pres g Φ hΦs⟩
  have hloc : ∀ f, Rest (evFin F v) f Rd → ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (tens (evFin F v) f Rd) = cf (Matrix.fromCols γ₁ γ₂) • tens (evFin F v) f Rd →
      schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) f = cf (Matrix.fromCols γ₁ γ₂) • f := by
    intro f hf γ₁ h₁ γ₂ h₂ h
    refine eq_of_tens v hf.1 hRd0 ?_
    rw [GlobalTheory.VacTransport.tens_smul, ← h]
    exact (GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (at_fromCols v (hat _ h₁) (hat _ h₂)) f Rd hf).symm
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo co v γ₁).1 (GlobalTheory.LatVac.locCo co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo co v γ₁).2 (-(GlobalTheory.LatVac.locCo co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X Y v co hX hY
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v co ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hφ0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ t * star (φ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ₁ φd
    (fun i => hloc φ₁ hrest₁ _ i.1.2 _ i.2.2 (hT ▸ h2 _ i.1.2 _ i.2.2))
    (fun i => hloc φd hrest _ i.1.2 _ i.2.2 (hΦt ▸ h1 _ i.1.2 _ i.2.2)) hφd0
  exact ⟨c', by rw [hT, hc', GlobalTheory.VacTransport.tens_smul, ← hΦt]⟩

end GlobalTheory.DblVacLineTransp

namespace GlobalTheory.DblVacLineSplitTransp

open GlobalTheory.DblVacLineTransp

end GlobalTheory.DblVacLineSplitTransp

end
end

