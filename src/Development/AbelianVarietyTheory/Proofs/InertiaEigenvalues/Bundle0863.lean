module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockEmbeddingGLTorusElementZeroPadded
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

section Block

variable {R S : Type} [CommRing R] [CommRing S] {j n : ℕ}

theorem blockGL_cornerGL (hj : j ≤ n) (s : R →ₙ+* S) (g : GL (Fin j) R) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (cornerGL j s g) =
      cornerGL n s (GroundTheory.Automorphic.FourierWhittaker.blockGL hj g) := by
  ext a b
  change GroundTheory.Automorphic.FourierWhittaker.blockMat hj
      ((1 : Matrix (Fin j) (Fin j) S) - (1 : Matrix (Fin j) (Fin j) R).map s + (g : Matrix (Fin j) (Fin j) R).map s) a b =
    (1 : Matrix (Fin n) (Fin n) S) a b - s ((1 : Matrix (Fin n) (Fin n) R) a b) +
      s (GroundTheory.Automorphic.FourierWhittaker.blockMat hj (g : Matrix (Fin j) (Fin j) R) a b)
  rw [GroundTheory.Automorphic.FourierWhittaker.blockMat_apply, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp only [dif_pos ha, dif_pos hb, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.one_apply,
        Fin.ext_iff]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.one_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.one_apply]
    · simp [ha, hab, Matrix.one_apply]

theorem blockGL_diagPow (hj : j ≤ n) (ϖ : Rˣ) (v : Fin j → ℕ) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL hj (diagPow ϖ v) = diagPow ϖ (GlobalTheory.RSnmUnf.padNat (n := n) v) := by
  ext a b
  rw [GroundTheory.Automorphic.FourierWhittaker.coe_blockGL, GroundTheory.Automorphic.FourierWhittaker.blockMat_apply]
  simp only [diagPow, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.diagonalRingHom_apply]
  by_cases ha : a.val < j
  · by_cases hb : b.val < j
    · simp [ha, hb, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, Fin.ext_iff, MulEquiv.piUnits]
    · have hab : a ≠ b := fun h => hb (h ▸ ha)
      simp [ha, hb, hab, Matrix.diagonal_apply]
  · by_cases hab : a = b
    · subst hab; simp [ha, Matrix.diagonal_apply, GlobalTheory.RSnmUnf.padNat, MulEquiv.piUnits]
    · simp [ha, hab, Matrix.diagonal_apply]

theorem padNat_eq_zero_iff {m n : ℕ} (hmn : m ≤ n) (v : Fin m → ℕ) :
    GlobalTheory.RSnmUnf.padNat (n := n) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h ⟨i.val, by omega⟩
    simpa [GlobalTheory.RSnmUnf.padNat, i.isLt] using this
  · rintro rfl
    exact GlobalTheory.RSnmUnf.padNat_zero

end Block

theorem blockGL_tl {E : Type} [Field E] [NumberField E] (m r : ℕ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) :
    GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.JSW.tl ϖ l) =
      GlobalTheory.JSW.tl ϖ (l.mapRange GlobalTheory.RSnmUnf.padNat GlobalTheory.RSnmUnf.padNat_zero) := by
  have hsupp : (l.mapRange (GlobalTheory.RSnmUnf.padNat (n := m + r + 1 + 1)) GlobalTheory.RSnmUnf.padNat_zero).support = l.support := by
    ext w
    simp only [Finsupp.mem_support_iff, Finsupp.mapRange_apply, ne_eq]
    rw [padNat_eq_zero_iff (by omega)]
  unfold tl
  rw [hsupp, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, Finsupp.mapRange_apply]
  rw [finGL, locGL, blockGL_cornerGL, blockGL_cornerGL, blockGL_diagPow]
  rfl

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslate
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CellPw

variable {E : Type} [Field E] [NumberField E]

theorem rowInf_tl [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n) (r : Fin n) :
    (fun i => pInf E ((GlobalTheory.CellDec.tl n ϖ l * g).val r i)) = fun i => pInf E (g.val r i) := by
  have h : GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l * g) = GeneralLinearGroup.map (pInf E) g := by
    rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul]
  funext i
  exact congrArg (fun M : GL (Fin n) (Cinf E) => M.val r i) h

theorem bInt_of_not_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∉ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h = 0 := by
  simp [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, Set.indicator_of_notMem hm]

theorem bInt_of_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∈ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h =
      ENNReal.ofReal (‖GlobalTheory.JSW.whit F (h * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (fun i => pInf E (h.val ℓ i))))⁻¹)‖ ^ 2 *
        ‖Φ (fun i => pInf E (h.val ℓ i))‖ * (ideleModule E (GeneralLinearGroup.det h) : ℝ) ^ x) := by
  rw [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Set.indicator_of_mem hm,
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_conj]
  ring

theorem prod_supp_add {n : ℕ} (q : HeightOneSpectrum (𝓞 E) → ℝ) (hq : ∀ v, q v ≠ 0) (f : (Fin n → ℤ) →+ ℤ)
    (a b : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    ∏ v ∈ (a + b).support, q v ^ f ((a + b) v) =
      (∏ v ∈ a.support, q v ^ f (a v)) * ∏ v ∈ b.support, q v ^ f (b v) := by
  have := Finsupp.prod_add_index' (f := a) (g := b) (h := fun v y => q v ^ f y) (fun v => by simp)
    (fun v y₁ y₂ => by simp [zpow_add₀ (hq v)])
  simpa [Finsupp.prod] using this

def wtSHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := GlobalTheory.CellDec.wtS n
  map_zero' := by simp [GlobalTheory.CellDec.wtS]
  map_add' a b := by
    simp only [GlobalTheory.CellDec.wtS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp <;> ring

def negSumHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun a := -∑ i, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]; ring


omit [Field E] [NumberField E] in
theorem cell_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  intro E _ _ _ m T ϖ hϖ α F l₀ U Φ J hl₀ hU hK hN hprof hΦ hJ horb x g hg l
  have hνT : ∀ v ∈ T, (l.1 - l₀.1) v = 0 := fun v hv => by simp [l.2 v hv, l₀.2 v hv]
  let ν : GlobalTheory.CellDec.abelian₂ E (m + 1) T := ⟨l.1 - l₀.1, hνT⟩
  have hνl : l₀.1 + ν.1 = l.1 := by simp [ν]
  have hνw : ∀ w, ν.1 w (Fin.last m) = l.1 w (Fin.last m) := fun w => by simp [ν, hl₀ w]
  by_cases hneg : ∃ w, l.1 w (Fin.last m) < 0
  · obtain ⟨w, hw⟩ := hneg
    have hwT : w ∉ T := fun h => by simp [l.2 w h] at hw
    rw [bInt_of_not_mem _ _ _ _ _ _ _ (_root_.GlobalTheory.CellDec.lastRow_sub_notMem_latt E m T ϖ hϖ J hJ g hg l w hw)]
    have h2 : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = 0 := by
      refine Finset.prod_eq_zero (i := w) ?_ ?_
      · rw [Finsupp.mem_support_iff]
        intro h
        have := congrFun h (Fin.last m)
        simp [hl₀ w] at this
        omega
      · rw [dite_eq_right hwT]
        exact GlobalTheory.RSCell.locFac_of_neg _ _ _ (i := Fin.last m) (by simp [hl₀ w]; exact hw)
    rw [h2]
    simp
  push_neg at hneg
  have hl₀n : ∀ w, 0 ≤ l₀.1 w (Fin.last m) := fun w => (hl₀ w).ge
  have hposl := _root_.GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff E m T ϖ hϖ J hJ g hg l hneg
  have hposl₀ := _root_.GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff E m T ϖ hϖ J hJ g hg l₀ hl₀n
  by_cases hI : (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J
  swap
  · rw [bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl.1 h)),
      bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl₀.1 h))]
    simp
  rw [bInt_of_mem _ _ _ _ _ _ _ (hposl.2 hI), bInt_of_mem _ _ _ _ _ _ _ (hposl₀.2 hI),
    rowInf_tl, rowInf_tl]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E (g.val (Fin.last m) i) with hu
  by_cases hΦu : Φ u = 0
  · simp [hΦu]
  have hunit : IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) :=
    GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦ (subset_tsupport _ hΦu))
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell E m T ϖ F U J hU hK hN horb g hg hunit hI
  rw [hpl l, hpl l₀, _root_.GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul E (m + 1) ϖ hϖ l.1 g, _root_.GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul E (m + 1) ϖ hϖ l₀.1 g]
  have hpr := hprof p hp ν (fun w => by rw [hνw]; exact hneg w)
  rw [hνl] at hpr
  rw [hpr]

  have hq : ∀ v : HeightOneSpectrum (𝓞 E), (qV E v : ℝ) ≠ 0 := fun v => by
    rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < (qV E v : ℝ) := fun v =>
    lt_of_le_of_ne (Nat.cast_nonneg _) (hq v).symm
  have hcell : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = ENNReal.ofReal (∏ w ∈ ν.1.support,
      ((qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) * (qV E w : ℝ) ^ (-((∑ i, (ν.1 w i : ℝ)) * x)) *
        ‖(if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (ν.1 w))‖ ^ 2)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwT : w ∉ T := fun h => (Finsupp.mem_support_iff.1 hw) (hνT w h)
    rw [dite_eq_right hwT, dite_eq_right hwT, ← _root_.GlobalTheory.RSCell.locFac_eq_wtS_sphZ (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)) m (α ⟨w, hwT⟩) x (ν.1 w) (by rw [hνw]; exact hneg w),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have hd0 : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ), 0 ≤ GlobalTheory.CellDec.dinv (m + 1) k := fun k =>
    Finset.prod_nonneg fun v _ => (zpow_pos (hqpos v) _).le
  rw [hcell, ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (mul_nonneg (hd0 _) <| mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)
      ((ideleModule E (GeneralLinearGroup.det g)).2.le)) _))]
  congr 1
  have hd : GlobalTheory.CellDec.dinv (m + 1) l.1 = GlobalTheory.CellDec.dinv (m + 1) l₀.1 *
      ∏ w ∈ ν.1.support, (qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) := by
    rw [← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (wtSHom (m + 1)) l₀.1 ν.1
  have hQ : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ),
      ∏ v ∈ k.support, ((qV E v : ℝ) ^ ∑ i, k v i)⁻¹ = ∏ v ∈ k.support, (qV E v : ℝ) ^ negSumHom (m + 1) (k v) := by
    intro k
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← _root_.zpow_neg]; rfl
  have hQl : ∏ v ∈ l.1.support, ((qV E v : ℝ) ^ ∑ i, l.1 v i)⁻¹ =
      (∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹) * ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ := by
    rw [hQ, hQ, hQ, ← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (negSumHom (m + 1)) l₀.1 ν.1
  have hQν : (∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
      ∏ v ∈ ν.1.support, (qV E v : ℝ) ^ (-((∑ i, (ν.1 v i : ℝ)) * x)) := by
    have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)),
        (∏ v ∈ s, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
          ∏ v ∈ s, (((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Real.mul_rpow (inv_pos.2 (zpow_pos (hqpos a) _)).le
            (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le), ih]
    rw [hprod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_neg (hqpos v).le, ← Real.rpow_mul (hqpos v).le]
    push_cast
    ring_nf
  have hD := ((ideleModule E (GeneralLinearGroup.det g)).2 : (0 : ℝ) < _)
  have hQ₀ : 0 ≤ ∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  have hQν0 : 0 ≤ ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  rw [hd, hQl, Real.mul_rpow (mul_nonneg hQ₀ hQν0) hD.le, Real.mul_rpow hQ₀ hQν0, hQν, Real.mul_rpow hQ₀ hD.le,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.CellPw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFormsBaseLevelLeSpanIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000open Formalism.L2.Host (embLL0)

noncomputable section

namespace GlobalTheory.BaseSpan

variable {D : D7} {S T : HSp D}

theorem pq_le {B : Base S T} (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ T.rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

theorem coefLat_le_valSpace {B : Base S T} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} {y : Bridge.Gf S}
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) : P ∈ B.valSpace :=
  hspan ▸ Submodule.subset_span hP

theorem tr_mem_mtLat {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {ψ : Twist D Circle}
    (hlam : ∀ k, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ O) {y : Bridge.Gf S}
    (hf : Finite (Bridge.stab (Bridge.ratF S) (B.levJ ψ) y))
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) :
    GlobalTheory.LawTrace.tr (Bridge.ratF S) (B.act.comp (GQ S).subtype) (B.levJ ψ) (B.levLam ψ) y P ∈ B.mtLat σ emb O ψ := by
  refine (Base.mem_mtLat B σ emb O).2 ⟨Submodule.mem_inf.2 ⟨?_, GlobalTheory.LawTrace.mem_lawForms_tr hf P⟩, fun x => ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => GlobalTheory.LawTrace.tr_mem hf P x B.valSpace fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (coefLat_le_valSpace hspan hP))
  · refine GlobalTheory.LawTrace.tr_mem hf P x (B.coefLat σ emb O x) fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    have hx : x = Bridge.ratF S γ * y * ((⟨_, h⟩ : B.levJ ψ) : Bridge.Gf S) := by
      change x = Bridge.ratF S γ * y * ((Bridge.ratF S γ * y)⁻¹ * x)
      group
    have h1 := Base.act_mem_coefLat hB.frame hc γ y _ (Base.mem_St_of_mem_levJ (B := B) h) hP
    rw [← hx] at h1
    have h2 := Submodule.smul_mem (B.coefLat σ emb O x) (⟨_, hlam ⟨_, h⟩⟩ : O) h1
    exact h2

end GlobalTheory.BaseSpan

namespace GlobalTheory.BaseSpan

theorem tw_one_good {D : D7} {ρ : Setup D.ntw} (i : D.ntw.Tw) (b : Bool) :
    (ρ.tw i b 0 ∅ 1).Good ∧ (ρ.tw i b 0 ∅ 1).Q = ∅ := by
  have hc : (ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hq : (ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  refine ⟨⟨?_, fun x => ?_, fun a => ?_, ?_, fun x _ _ _ _ => ?_, fun PP h => ?_⟩, hq⟩
  · rw [hc, MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ
  · rw [hc]; rfl
  · rw [hc]; rfl
  · rw [hq]; exact splitSet_empty
  · rw [hc]; rfl
  · rw [hq] at h; exact absurd h (Finset.notMem_empty _)

theorem formsC_le_span_mt : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)) := by
  intro D X E Y i j b F hF
  have hρ : Y.Z.ρ.Good := Y.Z.good
  have hB : (Y.Z.ρ.B i j b).Good := hρ.base i j b
  obtain ⟨hψ, hψQ⟩ := tw_one_good (ρ := Y.Z.ρ) i b
  have hcls := hρ.classes i j b (Y.Z.ρ.tw i b 0 ∅ 1) hψ (by rw [hψQ]; exact Base.admissible_empty_of_good hB)
  have hlam : ∀ k, (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := fun k => _root_.GlobalTheory.LamVal.levLam_mem_coef D X E Y i j b k
  have hL := (Submodule.mem_inf.1 hF).2
  rw [GlobalTheory.LawTrace.eq_sum_tr hcls.reps hcls.stab hL]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
  have hspan : Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D) (Y.Z.ρ.eOk i b 0).range
      (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) = (Y.Z.ρ.B i j b).valSpace :=
    (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS _
      (embLL0 D) (labLL0 D) _ _ hB.wt (pq_le hB) (hρ.isCoefRing_k i b 0)
      (GlobalTheory.LatFull.latAt_isFullLattice D Y.Z.ρ hρ i j b _)).2
  have hFy : F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) ∈ Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D)
      (Y.Z.ρ.eOk i b 0).range (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    rw [hspan]
    exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hF).1) _ trivial
  generalize F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) = v at hFy ⊢
  induction hFy using Submodule.span_induction with
  | mem P hP =>
    exact Submodule.subset_span (tr_mem_mtLat hB (hρ.isCoefRing_k i b 0) hlam (hcls.stab c) hspan hP)
  | zero =>
    rw [GlobalTheory.LawTrace.tr_zero]
    exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [GlobalTheory.LawTrace.tr_add (hcls.stab c)]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [GlobalTheory.LawTrace.tr_smul]
    exact Submodule.smul_mem _ _ hP

end GlobalTheory.BaseSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
namespace GlobalTheory.ConjLocCsd

theorem plMap_conj_eq {R : Ranks} (Hs : Host R) (w w' : HeightOneSpectrum (𝓞 Hs.E)) (h : IsConjPl Hs w w') :
    CT.plMap (Hs.conj : Hs.E ≃+* Hs.E) w = w' := by
  ext y
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E)
  set x := (RingOfIntegers.mapRingEquiv j).symm y with hx
  have hy : RingOfIntegers.mapRingEquiv j x = y := by rw [hx, RingEquiv.apply_symm_apply]
  have hyx : (y : Hs.E) = Hs.conj (x : Hs.E) := by rw [← hy]; rfl
  rw [← hy, CT.mem_plMap, hy]
  exact h x y hyx

theorem main : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  intro R Hs μ hμ w w' hc
  have hcsd := hμ.1 w w' hc
  obtain rfl := plMap_conj_eq Hs w w' hc
  set j : Hs.E ≃+* Hs.E := (Hs.conj : Hs.E ≃+* Hs.E) with hj
  set i := CT.compEquiv j w with hi
  have hcont : Continuous i := CT.continuous_compEquiv j w
  have halg : ∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x) := fun x => CT.compEquiv_algebraMap j w x
  refine ⟨i, hcont, halg, ?_⟩
  obtain ⟨ξ, -, huniq, -⟩ := _root_.GlobalTheory.HeckeComp.main Hs.E μ⁻¹ w
  set ψ₁ : (w.adicCompletion Hs.E)ˣ →* ℂˣ := (μ.loc (CT.plMap j w)).comp (Units.map i.toRingHom.toMonoidHom) with hψ₁
  have h1 : IsComp μ⁻¹ w ψ₁ := by
    refine ⟨?_, fun x => ?_⟩
    · have hc' : Continuous (Units.map i.toRingHom.toMonoidHom) := Units.continuous_map hcont
      exact (ParLaws.isSmoothChar_loc μ (CT.plMap j w)).preimage hc'
    · have hu : Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap Hs.E (w.adicCompletion Hs.E)).toMonoidHom x)
          = Units.map (algebraMap Hs.E ((CT.plMap j w).adicCompletion Hs.E)).toMonoidHom (Units.map (Hs.conj : Hs.E ≃+* Hs.E).toRingHom.toMonoidHom x) := by
        apply Units.ext
        exact halg (x : Hs.E)
      rw [hψ₁, MonoidHom.comp_apply, hu]
      have := hcsd x
      exact this
  have h2 : IsComp μ⁻¹ w ((μ⁻¹).loc w) := ⟨ParLaws.isSmoothChar_loc _ w, fun x => rfl⟩
  have he : ψ₁ = (μ⁻¹).loc w := (huniq _ h1).trans (huniq _ h2).symm
  intro x
  have := congrArg (fun f => f x) he
  have hinv : (μ⁻¹).loc w x = (μ.loc w x)⁻¹ := rfl
  simpa only [hψ₁, MonoidHom.comp_apply, hinv] using this

end GlobalTheory.ConjLocCsd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem GlobalTheory.WeilDeligne.WDRep.rho_apply_of_mk_eq_lpOfChar {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {n : ℕ} (b : WDRep h (Fin n → ℂ)) (χ : Weil h →* ℂˣ) (hχ : WeilDeligne.IsSmooth χ)
    (hb : WD.mk b = WD.lpOfChar h χ hχ) (σ : Weil h) (v : Fin n → ℂ) : b.ρ σ v = (χ σ : ℂ) • v := by
  obtain ⟨e, h1, -⟩ := WD.mk_eq_mk.1 hb
  apply e.injective
  rw [h1, map_smul]
  ext k
  simp
end

