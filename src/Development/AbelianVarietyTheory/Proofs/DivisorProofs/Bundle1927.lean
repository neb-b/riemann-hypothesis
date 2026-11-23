module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivariance
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalBox

open Matrix

section Local

variable {F : Type} [Field F] [NumberField F]

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem tens_box (v : Pl (F := F)) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_box (v : Pl (F := F)) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_ne (v : Pl (F := F)) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

end Local

theorem scal_diag_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd
    hcd h hh gd hgd
  have hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι

  set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def
  have h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ (fun _ => 0) = 1 := by
    rw [hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
      {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hne : ι φ₀ ≠ 0 := by
    intro e
    have e0 : φ₀ = 0 := hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])
    have e1 := congrFun e0 (fun _ => 0)
    rw [hφ₀0] at e1
    exact one_ne_zero e1
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def
  have h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v) := conj_mem_SB h0
  have hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀ := funext fun x => Complex.conj_conj _

  have h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    have e : mat (1 : UA σ X.J) = 1 := rfl
    rw [e, sub_self, smul_zero]
  obtain ⟨φ₁, ⟨h1, hA1⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0
  have hk := hκ h hh φ₀ h0 φ₁ h1 hA1

  have hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v) := by
    intro u hu
    rw [hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]
    simp
  obtain ⟨Φ₁, hΦ₁, hAd⟩ := hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v
  have hRb := rest_box v (hR φ₀ h0) (hR φ₂ h2)
  have e := hAd _ hRb
  rw [tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box] at e
  have h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0 := by
    show R 0 * R 0 ≠ 0
    exact mul_ne_zero hR0 hR0
  have eΦ : Φ₁ = boxFun φ₁ φ₂ := eq_of_tens_ne v hRb.1 h0r e.symm

  have hs := hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd
  rw [eΦ] at hs
  set L := locMat t c h with hL
  have hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1 := by
    show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) *
      (GlobalTheory.DblScal.dsum c).val = _
    rw [hgd, hL, locMat_val, fromBlocks_map]
    simp only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  have hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
    have hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1 := by
      rw [hD, fromBlocks_multiply]
      simp [← fromBlocks_one]
    calc ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val
        = (Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val) *
            ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val := by rw [hm, Matrix.one_mul]
      _ = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1 := by
    rw [GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]
    simp
  have hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀ := by
    rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  have hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A := by
    intro A Bm; ext i j; rfl
  have hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm := by
    intro A Bm; ext i j; rfl
  have hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromCols Y₀ Y₀ := by
    rw [hT, Matrix.fromCols_mul_fromBlocks]
    simp [hY]
  have eY := congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)
  rw [hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2] at eY
  simp only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY
  have hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0 := mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)
  apply mul_right_cancel₀ hP0
  linear_combination eY

end GlobalTheory.DblScalBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplitting
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblLin

open Matrix

def schrLin {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def conjLin {Y Y' : Type} (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ)) : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ) where
  toFun φ := star (ι (star φ))
  map_add' f g := by rw [star_add, map_add (f := _), star_add]
  map_smul' a f := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem star_mem_SB {Y : Type} [TopologicalSpace Y] {f : Y → ℂ} (hf : f ∈ SB Y) : star f ∈ SB Y :=
  ⟨hf.1.comp star, hf.2.comp_left (g := star) (star_zero ℂ)⟩

theorem conjLin_bijOn {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ))
    (h : Set.BijOn ι (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ))) :
    Set.BijOn (conjLin ι) (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ)) := by
  refine ⟨fun φ hφ => star_mem_SB (h.mapsTo (star_mem_SB hφ)), fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
  · have e' : ι (star φ) = ι (star φ') := star_injective e
    exact star_injective (h.injOn (star_mem_SB hφ) (star_mem_SB hφ') e')
  · obtain ⟨φ, hφ, e⟩ := h.surjOn (star_mem_SB hg)
    refine ⟨star φ, star_mem_SB hφ, ?_⟩
    show star (ι (star (star φ))) = g
    rw [star_star, e, star_star]

def colsHomeo (m a b k : Type) [TopologicalSpace k] :
    Matrix m (a ⊕ b) k ≃ₜ Matrix m a k × Matrix m b k where
  toFun Y := (Y.submatrix id Sum.inl, Y.submatrix id Sum.inr)
  invFun p := Matrix.fromCols p.1 p.2
  left_inv Y := by ext i (j | j) <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases j with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd

theorem eqOn_SB_of_box {k : Type} [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
    {κ : Type} [Fintype κ] {N : Type} [AddCommGroup N] [Module ℂ N] (L₁ L₂ : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] N)
    (h : ∀ a ∈ SB (κ → k), ∀ b ∈ SB (κ → k), L₁ (boxFun a b) = L₂ (boxFun a b)) :
    ∀ φ ∈ SB (κ ⊕ κ → k), L₁ φ = L₂ φ := by
  intro φ hφ
  let e : (κ ⊕ κ → k) ≃ₜ (κ → k) × (κ → k) := Homeomorph.sumArrowHomeomorphProdArrow
  let M₁ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₁ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  let M₂ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₂ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  have hM : M₁ = M₂ := LinearMap.ext_on_range (GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top _ _)
    fun q => h q.1.1 q.1.2 q.2.1 q.2.2
  have := LinearMap.congr_fun hM (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)
  have e2 : ((GlobalTheory.LocFlat.CFac.comapH e (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)).1 : (κ ⊕ κ → k) → ℂ) = φ := by
    funext x
    simp only [GlobalTheory.LocFlat.CFac.comapH_apply, Homeomorph.symm_apply_apply]
  simp only [M₁, M₂, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [← e2]
  exact this

theorem coord_inl {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inl = B * A.toCols₁ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem coord_inr {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inr = B * A.toCols₂ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem dblLin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair v t b c ι hι dd hdd
  classical
  have hψ1 : ∀ x, ‖B.ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std
  have hψc : Continuous B.ψ := hpair.base.std.1
  have hψv : ∀ x, ‖GlobalTheory.LatVac.psiAt B.ψ v x‖ = 1 := fun x => hψ1 _
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  obtain ⟨ιd, hbij, hprod⟩ := _root_.GlobalTheory.SBProdExt.exists_linear_bijOn_prod (Homeomorph.sumArrowHomeomorphProdArrow (X := Fv F v)
    (ι := Fin n × Fin d) (ι' := Fin n × Fin d)) (colsHomeo (Fin n) (Fin d) (Fin d) (Fv F v)) ι (conjLin ι) hι.bij
    (conjLin_bijOn ι hι.bij)
  have hbox : ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
      ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) * star (ι (star φ₂) (Y.submatrix id Sum.inr)) :=
    fun φ₁ h₁ φ₂ h₂ => hprod φ₁ h₁ φ₂ h₂

  have hsplit : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.LatVac.locCo dd v u = (Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).1 (GlobalTheory.LatVac.locCo M.co v u.toCols₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).2 (-(GlobalTheory.LatVac.locCo M.co v u.toCols₂).2)) := by
    intro u
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
  have hat1 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → At (evFin F v) u.toCols₁ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inl j)
  have hat2 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → At (evFin F v) u.toCols₂ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inr j)
  have hmap1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), u.map π = 0 →
      u.toCols₁.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inl j)
  have hmap2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), u.map π = 0 →
      u.toCols₂.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inr j)
  have hc1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), (u.map π).toCols₁ = u.toCols₁.map π :=
    fun u π => rfl
  have hc2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (π : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), (u.map π).toCols₂ = u.toCols₂.map π :=
    fun u π => rfl

  have hloc : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
        φ₁ = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ := fun u hu φ hφ φ₁ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (hA r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ r hr)

  have hschr : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ a ∈ SB (Fin n × Fin d → Fv F v),
      ∀ b' ∈ SB (Fin n × Fin d → Fv F v),
      ιd (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) (boxFun a b')) = fun Y =>
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₁) a) (Y.submatrix id Sum.inl) *
          star (ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b'))
            (Y.submatrix id Sum.inr)) := by
    intro u a ha b' hb
    have e0 : boxFun a b' = boxFun a (fun x => star ((star b') x)) := by
      funext x; simp [boxFun]
    rw [hsplit u, e0, GlobalTheory.DblVacLine.schr_box _ hψv]
    rw [hbox _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x))
      (star_mem_SB (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb)))]
    have e1 : (star fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x)) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') := by
      funext x; simp
    rw [e1]
  refine ⟨ιd, ⟨hbij, ?_, ?_⟩, hbox⟩
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA Y
    rw [hloc u hu φ hφ φ₁ hA]
    set sh := (b⁻¹).val * u.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    have key := eqOn_SB_of_box (ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (LinearMap.funLeft ℂ ℂ (fun Y => Y + sh) ∘ₗ ιd) (fun a ha b' hb => ?_) φ hφ
    · exact congrFun key Y
    show ιd (schr _ _ (boxFun a b')) = fun Y => ιd (boxFun a b') (Y + sh)
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    funext Y
    have t1 := hι.trans u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) (Y.submatrix id Sum.inl)
    have t2 := hι.trans u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) (Y.submatrix id Sum.inr)
    have s1 : (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + (b⁻¹).1 * u.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + sh.submatrix id Sum.inl from rfl, coord_inl, hc1]
    have s2 : (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + (b⁻¹).1 * u.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + sh.submatrix id Sum.inr from rfl, coord_inr, hc2]
    rw [t1, t2]
    beta_reduce
    rw [s1, s2]
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA x hx hx0
    rw [hloc u hu φ hφ φ₁ hA]
    set P := (b⁻¹).val * x.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    set z := B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) x u)
    have key := eqOn_SB_of_box (LinearMap.proj P ∘ₗ ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (z • (LinearMap.proj P ∘ₗ ιd)) (fun a ha b' hb => ?_) φ hφ
    · exact key
    show ιd (schr _ _ (boxFun a b')) P = z * ιd (boxFun a b') P
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    have p1 : P.submatrix id Sum.inl = (b⁻¹).1 * x.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inl, hc1]
    have p2 : P.submatrix id Sum.inr = (b⁻¹).1 * x.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inr, hc2]
    have m1 := hι.mult u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) x.toCols₁ (hat1 x hx) (hmap1 x _ hx0)
    have m2 := hι.mult u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) x.toCols₂ (hat2 x hx) (hmap2 x _ hx0)
    beta_reduce
    rw [p1, p2, m1, m2]
    have hs : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) x u =
        symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x.toCols₁ u.toCols₁ -
          symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x.toCols₂ u.toCols₂ := by
      conv_lhs => rw [← Matrix.fromCols_toCols x, ← Matrix.fromCols_toCols u]
      exact GlobalTheory.DblVacLine.symp_dbl _ _ _ _ _ _ _ _
    have hz : z = B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x.toCols₁ u.toCols₁) *
        star (B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x.toCols₂ u.toCols₂)) := by
      rw [GlobalTheory.DblVacLine.star_eq_neg B.ψ hψ1, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← hs]
    rw [hz, star_mul]
    dsimp only [cA, incM]
    ring

end GlobalTheory.DblLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

namespace SplitSurj

theorem dbl_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem dbl_skew {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = -J i j) :
    ∀ i j, σ (dbl J j i) = -dbl J i j := by
  rintro (i | i) (j | j) <;> simp [dbl, hJ]

theorem isUnit_det_dbl_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    (t : E →ₐ[F] K) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : J.det ≠ 0) : IsUnit ((dbl J).map t).det := by
  have h1 : (J.map t).det ≠ 0 := by
    rw [show J.map t = (t : E →+* K).mapMatrix J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ
  rw [dbl, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.det_fromBlocks_zero₂₁]
  refine isUnit_iff_ne_zero.2 (mul_ne_zero h1 ?_)
  rw [show ((-J).map t) = -(J.map t) by ext i j; simp, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1

end SplitSurj

open SplitSurj in
theorem locMatD_surjOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  intro F E _ _ _ _ _ σ h d J hdet hJ v t c A _
  have hK := isUnit_det_dbl_map t J hdet
  have skew := dbl_skew σ J hJ
  let A' : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c * A * (dsum c)⁻¹
  let G : GL (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.LeviIdx.adelicGL h t (dbl J) hK A'
  have hu : G ∈ UG (cA σ) (dbl (incM F J)) := by
    show (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl_incM]
    exact GlobalTheory.LeviIdx.adelicGL_unitary h t (dbl J) hK skew A'
  refine ⟨⟨G, hu⟩, GlobalTheory.LeviIdx.adelicGL_at h t (dbl J) hK A', ?_⟩
  change (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) G * dsum c = A
  rw [GlobalTheory.LeviIdx.adelicGL_map_piW]
  show (dsum c)⁻¹ * (dsum c * A * (dsum c)⁻¹) * dsum c = A
  group

end GlobalTheory.DblScal

end
end

