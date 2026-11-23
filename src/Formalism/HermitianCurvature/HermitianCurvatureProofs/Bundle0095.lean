module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0089
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def DTExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂

def DTStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ →
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ →
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ →
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

theorem datumTransit_of_cut (hE : DTExists) (hS : DTStab) : DatumTransit := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨h, hh, h', hh', e1, e2, e3⟩ := hE k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  exact ⟨h, hh, h', hh', e1, e2, e3, hS k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSGen
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {n : ℕ}

def cols (x : Fin n → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun p i => x i p

theorem cols_mulVec (x : Fin n → Fin n → ℂ) (c : Fin n → ℂ) : cols x *ᵥ c = ∑ i, c i • x i := by
  funext p
  simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem cols_mulVec_single (x : Fin n → Fin n → ℂ) (i : Fin n) : cols x *ᵥ Pi.single i 1 = x i := by
  rw [cols_mulVec, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mul_cols (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    A * cols x = cols (fun i => A *ᵥ x i) := by
  ext p i
  simp [cols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_cols (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    (cols x)ᴴ * H * cols x = Matrix.of fun j i => herm H (x i) (x j) := by
  ext j i
  rw [Matrix.mul_assoc, mul_cols]
  simp [cols, Matrix.mul_apply, herm, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq {H : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : (cols x)ᴴ * H * cols x = H := by
  rw [gram_cols]
  ext j i
  exact hx i j

theorem cols_unit {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) {x : Fin n → Fin n → ℂ}
    (hx : ∀ i j, herm H (x i) (x j) = H j i) : IsUnit (cols x).det := by
  have h := congrArg Matrix.det (gram_eq hx)
  rw [Matrix.det_mul] at h
  rw [← h] at hH
  exact isUnit_of_mul_isUnit_right hH

theorem wittGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x y : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (hy : ∀ i j, herm H (y i) (y j) = H j i) :
    ∃ g ∈ UH H, ∀ i, g *ᵥ x i = y i := by
  have hX := cols_unit hH hx
  have gx := gram_eq hx
  have gy := gram_eq hy
  have e1 : (cols x)⁻¹ * cols x = 1 := Matrix.nonsing_inv_mul _ hX
  have e2 : cols x * (cols x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hX
  refine ⟨cols y * (cols x)⁻¹, ?_, ?_⟩
  · show (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹) = H
    calc (cols y * (cols x)⁻¹)ᴴ * H * (cols y * (cols x)⁻¹)
        = ((cols x)⁻¹)ᴴ * ((cols y)ᴴ * H * cols y) * (cols x)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = ((cols x)⁻¹)ᴴ * ((cols x)ᴴ * H * cols x) * (cols x)⁻¹ := by rw [gy, gx]
      _ = (cols x * (cols x)⁻¹)ᴴ * H * (cols x * (cols x)⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [e2]; simp
  · intro i
    calc (cols y * (cols x)⁻¹) *ᵥ x i = (cols y * (cols x)⁻¹) *ᵥ (cols x *ᵥ Pi.single i 1) := by
          rw [cols_mulVec_single]
      _ = y i := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, e1, Matrix.mul_one, cols_mulVec_single]

theorem extGram (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det) (x : Fin n → Fin n → ℂ)
    (hx : ∀ i j, herm H (x i) (x j) = H j i) (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i, A *ᵥ x i = B *ᵥ x i) : A = B := by
  have hX := cols_unit hH hx
  have e : A * cols x = B * cols x := by
    rw [mul_cols, mul_cols]
    congr 1
    funext i
    exact h i
  calc A = A * cols x * (cols x)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
    _ = B := by rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts
section
open Matrix Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ

def bigPt {n : ℕ} (d : Fin n → ℂ) : C.LPt := List.ofFn fun i => (1, d i)

def BigCellVan : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → Top.IsRadOf P p.T.base 0 F →
    ∀ d : Fin (P.r + 1) → ℂ, (∀ i, d i ≠ 0) → p.V F (bigPt d) = 0

def DensCOfParts : Prop := KB.PhiZero → KB.KloostDens → BigCellVan → KB.DensC

namespace Dens

theorem ptEntry_ones (l : List ℂ) (a b : ℕ) :
    D.ptEntry (l.map fun c => (1, c)) a b = if a = b ∧ a < l.length then l.getD a 0 else 0 := by
  induction l generalizing a b with
  | nil => simp [D.ptEntry]
  | cons c l ih =>
    cases a <;> cases b <;> simp [D.ptEntry, ih]

theorem ptMatN_bigPt {n : ℕ} (d : Fin n → ℂ) : D.ptMatN (bigPt d) n = U.hMat 1 d := by
  ext a b
  have h : bigPt d = (List.ofFn d).map fun c => ((1 : ℕ), c) := by
    simp [bigPt, List.map_ofFn, Function.comp_def]
  simp only [D.ptMatN, h, ptEntry_ones, U.hMat, U.wP, Matrix.mul_diagonal, Matrix.of_apply,
    Equiv.Perm.one_apply, List.length_ofFn]
  by_cases hab : a = b
  · subst hab
    simp [List.getD_eq_getElem?_getD]
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [hab, hab']

theorem isLocPt_bigPt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) : D.IsLocPt (bigPt d) n := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [bigPt, List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hd i⟩
  · simp [D.ptSize, bigPt, List.map_ofFn, Function.comp_def, List.sum_ofFn]

end Dens

theorem density_constant_of_parts : DensCOfParts := by
  intro hPZ hKD hBV Wp Wq _ _ _ _ _ _ P p F hC hR a
  obtain ⟨Φ0, hs, hcs, hdet, hV⟩ := hPZ Wp Wq P p F hC
  by_cases ha : D.IsLocPt a (P.r + 1)
  · have key : ∀ n, D.ptSize a = n →
        ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN a n := by
      rintro n rfl
      obtain ⟨σ, d, -, h⟩ := Asm.exists_hMat a ha.1
      exact ⟨σ, d, h⟩
    obtain ⟨σ, d, hσd⟩ := key _ ha.2
    rw [hV a σ d ha hσd]
    refine hKD (P.r + 1) (Wq →L[ℂ] Wp) Φ0 hs hcs hdet ?_ a σ d ha hσd
    intro d' hd'
    rw [← hV (bigPt d') 1 d' (Dens.isLocPt_bigPt d' hd') (Dens.ptMatN_bigPt d').symm]
    exact hBV Wp Wq P p F hC hR d' hd'
  · unfold KB.Pl.V D.vecV
    rw [dite_eq_right (fun h => ha h.1)]

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

theorem pb_densC_of (hPZ : Formalism.FourierDecayAlt.KB.PhiZero) (hBV : PBJ.BigCellVan) : Formalism.FourierDecayAlt.KB.DensC :=
  PBJ.density_constant_of_parts hPZ kloosterman_density hBV

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DframeCommute
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section commute

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inWb_of_zero (hr : r = 0) (v : Fin (2 * r + k + 1) → ℂ) : inWb k r v := by
  subst hr; intro i hi; exfalso; have := i.isLt; omega

theorem prW_perp0 (hr : r = 0) (z v : Fin (2 * r + k + 1) → ℂ) (hvz : herm (Hpk k r) v z = 0) :
    D.prW k r z v = v := by
  rw [prW_eq, Wb_of_inWb (inWb_of_zero hr v), hvz, zero_div, zero_smul, sub_zero]

theorem herm_unit {g : B.Mat k r} (hg : g ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  conv_lhs => rw [show w = g *ᵥ (g⁻¹ *ᵥ w) by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]]
  exact herm_m0_mulVec_invariant g hg v _

theorem dframe_commute (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    (hdet : (Zhat k r S.z S.z' γ).det ≠ 0) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (m₀ * hB * m₀⁻¹) * γ * hB⁻¹ = γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  obtain ⟨⟨a1, ha1, h1⟩, ⟨a2, ha2, h2⟩, h3⟩ := hD
  have hz := S.z_mem
  have hz' := S.z'_mem
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have uγ := WeylGroupFacts.isUnit_of_uh hγ
  have uB := WeylGroupFacts.isUnit_of_uh hhB.1
  set ζ := (Zhat k r S.z S.z' γ).det with hζdef
  have hzν : herm (Hpk k r) S.z' ν' = 0 := herm_zν hνz
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; have := S.T'_pos; intro h; simp at h; linarith
  have hzz0' : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; have := S.T_pos; intro h; simp at h; linarith

  have hlast : ∀ b : Fin (r + 1), b = Fin.last r := fun b => Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
  have hfz : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)), fvec k r x b = x := by
    intro x b; rw [hlast b]; exact fvec_lastI x
  have hadj : ∀ a b : Fin (r + 1), (Zhat k r S.z S.z' γ).adjugate a b = 1 := by
    subst hr; intro a b
    rw [Matrix.adjugate_fin_one]; fin_cases a; fin_cases b; rfl
  have hcofR : D.cofR S γ = γ *ᵥ S.z' := by
    unfold D.cofR; subst hr; simp [hadj, hfz]
  have hcofL : D.cofL S γ = S.z := by
    unfold D.cofL; subst hr; simp [hadj, hfz]
  rw [hcofR, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h1
  rw [hcofL, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h2

  set c1 := herm (Hpk k r) (γ *ᵥ S.z') S.z / herm (Hpk k r) S.z S.z with hc1
  set c2 := herm (Hpk k r) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k r) S.z' S.z' with hc2
  have hγz' : γ *ᵥ S.z' = c1 • S.z + ((a1 : ℂ) * ζ) • (m₀ *ᵥ ν') := by rw [← h1]; abel
  have hγiz : γ⁻¹ *ᵥ S.z = c2 • S.z' + ((a2 : ℂ) * conj ζ) • ν' := by rw [← h2]; abel
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hmiz : m₀⁻¹ *ᵥ S.z = (μ : ℂ)⁻¹ • S.z' := by
    have : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
  set σ := m₀⁻¹ * γ with hσdef

  have hσz' : σ *ᵥ S.z' = (c1 * (μ : ℂ)⁻¹) • S.z' + ((a1 : ℂ) * ζ) • ν' := by
    rw [hσdef, ← Matrix.mulVec_mulVec, hγz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmiz,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec, smul_smul]
  have ha2ζ : (a2 : ℂ) * conj ζ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast ha2.ne') ?_
    simpa using hdet
  have hγν : γ *ᵥ ν' = ((a2 : ℂ) * conj ζ)⁻¹ • (S.z - c2 • (γ *ᵥ S.z')) := by
    have e : γ *ᵥ (γ⁻¹ *ᵥ S.z) = S.z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uγ, Matrix.one_mulVec]
    rw [hγiz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at e
    rw [← e]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha2ζ, one_smul]
  have hσν : σ *ᵥ ν' = (((a2 : ℂ) * conj ζ)⁻¹ * (μ : ℂ)⁻¹) • S.z' -
      (((a2 : ℂ) * conj ζ)⁻¹ * c2) • (σ *ᵥ S.z') := by
    simp only [hσdef, ← Matrix.mulVec_mulVec]
    rw [hγν, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hmiz, smul_sub, smul_smul, smul_smul]

  have hfix : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 → σ *ᵥ u = u := by
    intro u hu1 hu2
    have e1 : herm (Hpk k r) (γ *ᵥ u) S.z = 0 := by
      rw [herm_unit hγ, hγiz, B2x4.herm_add_right, B2x4.herm_smul_right, B2x4.herm_smul_right, hu1, hu2]
      simp
    have e2 : herm (Hpk k r) (γ *ᵥ u) (γ *ᵥ S.z') = 0 := by rw [herm_m0_mulVec_invariant γ hγ, hu1]
    have key := h3 (γ *ᵥ u) (fun a => ⟨by rw [hfz]; exact e1, by rw [hfz]; exact e2⟩)
    rw [prW_perp0 hr S.z _ e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec,
      prW_perp0 hr S.z' u hu1] at key
    rw [hσdef, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]

  have hBz' : hB *ᵥ S.z' = S.z' := hhB.2.2
  have hBperp : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 →
      herm (Hpk k r) (hB *ᵥ u) S.z' = 0 ∧ herm (Hpk k r) (hB *ᵥ u) ν' = 0 := by
    intro u h1u h2u
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hBz']
      rw [herm_m0_mulVec_invariant hB hhB.1, h1u]
    · conv_lhs => rw [← hBν]
      rw [herm_m0_mulVec_invariant hB hhB.1, h2u]

  have hcomm : σ * hB = hB * σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set α := herm (Hpk k r) v S.z' / herm (Hpk k r) S.z' S.z' with hα
    set β := herm (Hpk k r) v ν' with hβ
    set v0 := v - α • S.z' - β • ν' with hv0
    have hv0z : herm (Hpk k r) v0 S.z' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hνz, hα]
      field_simp; ring
    have hv0ν : herm (Hpk k r) v0 ν' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hzν, hνν, hβ]
      ring
    have hv : v = v0 + α • S.z' + β • ν' := by rw [hv0]; abel
    obtain ⟨hb1, hb2⟩ := hBperp v0 hv0z hv0ν
    rw [← Matrix.mulVec_mulVec v σ hB, ← Matrix.mulVec_mulVec v hB σ, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hBz', hBν, hfix v0 hv0z hv0ν,
      hfix (hB *ᵥ v0) hb1 hb2]
    rw [hσν, hσz']
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hBz', hBν]

  have hγσ : γ = m₀ * σ := by rw [hσdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
  rw [hγσ]
  calc m₀ * hB * m₀⁻¹ * (m₀ * σ) * hB⁻¹ = m₀ * hB * (m₀⁻¹ * m₀) * σ * hB⁻¹ := by simp only [Matrix.mul_assoc]
    _ = m₀ * (σ * hB) * hB⁻¹ := by rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.mul_one]

end commute

end Formalism.FourierDecayAlt.P.PBI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

end Formalism.FourierDecayAlt.P.S3dx6
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiRegOf
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_lt_a {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by
  have h1 := hG.2.2.2
  have h2 := ag_nonneg k r
  have h3 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem phiReg_of (hSch : SchurH) (hNI : NormIdSm) (hGG : GrowthG) (hDD : DecDD) (hBC : BeConv) :
    More.PhiReg := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hbe x hx
  have hS' := hS
  obtain ⟨hl, hds, -, hG, hw0, -, hT, -, hπ, hW, hN, hGm, hq⟩ := hS'
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hl hds hw0 x hx
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq
  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  · obtain ⟨v, hv, hlv⟩ := hA
    set cc : ℂ := ((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ with hcc
    have hlx : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        l (σ g x) = cc • (be z c π σ μW μN (σ g x) v) (l v) :=
      fun g hg => l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv
    refine ⟨?_, ?_, ?_⟩
    · have hc := (hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS).2.2.1 x hxs v (Or.inl hv)
      have hc2 : ContinuousOn (fun g => cc • (ContinuousLinearMap.apply ℂ Wp (l v))
          (be z c π σ μW μN (σ g x) v)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
        ((ContinuousLinearMap.apply ℂ Wp (l v)).continuous.comp_continuousOn hc).const_smul cc
      exact hc2.congr (fun g hg => hlx g hg)
    · obtain ⟨C, hC⟩ := hDD hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v hv
      have hI := hGG k r μG (aOf r h) hGm (ag_lt_a hG)
      have hfin := l1_quotient_integral_bound hds hW hN hGm hq hC hI
      have hb : ∀ᵐ g ∂νq, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ≤
          (‖cc‖ₑ * ‖l v‖ₑ) * ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
        filter_upwards [hae] with g hg
        rw [← enorm_eq_nnnorm, hlx _ hg]
        have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
        calc ‖cc • (be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ
            = ‖cc‖ₑ * ‖(be z c π σ μW μN (σ (Matrix.of g) x) v) (l v)‖ₑ := enorm_smul _ _
          _ ≤ ‖cc‖ₑ * (‖be z c π σ μW μN (σ (Matrix.of g) x) v‖ₑ * ‖l v‖ₑ) := by
            gcongr
            exact ContinuousLinearMap.le_opENorm _ _
          _ ≤ ‖cc‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
              ‖l v‖ₑ) := by gcongr
          _ = _ := by ring
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq
          ≤ ∫⁻ g, (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_mono_ae hb
        _ = (‖cc‖ₑ * ‖l v‖ₑ) *
              ∫⁻ g, ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN) ∂νq :=
            lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])
        _ < ⊤ := ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) hfin
    · have hN2 := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hxs v (Or.inl hv) (l v)).1
      have hfin : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v (l v)) < ⊤ := by
        rw [hN2]; exact ENNReal.ofReal_lt_top
      unfold PI.BesselPeriodGGP.l2SG at hfin ⊢
      calc ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq
          = ∫⁻ g, ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq := by
            apply lintegral_congr_ae
            filter_upwards [hae] with g hg
            rw [hlx _ hg, nnnorm_smul, ENNReal.coe_mul, mul_pow]
        _ = ((‖cc‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 *
              ∫⁻ g, ((‖be z c π σ μW μN (σ (Matrix.of g) x) v (l v)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq :=
            lintegral_const_mul' _ _ (by simp)
        _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin
  · push Not at hA
    have hz : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ g x) = 0 :=
      fun g hg => hA _ (dd_stable hds hg x hx)
    refine ⟨?_, ?_, ?_⟩
    · exact (continuousOn_const (c := (0 : Wp))).congr (fun g hg => hz g hg)
    · have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top
    · unfold PI.BesselPeriodGGP.l2SG
      have : ∫⁻ g, ((‖l (σ (Matrix.of g) x)‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 ∂νq = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with g hg; simp [hz _ hg])]
        simp
      rw [this]; exact ENNReal.zero_lt_top

end Formalism.FourierDecayAlt.P.S3dx4
end
end

