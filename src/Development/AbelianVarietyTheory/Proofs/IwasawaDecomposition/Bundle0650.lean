module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem vmv_mul_vmv (a α b β : Fin n → k) :
    vecMulVec a α * vecMulVec b β = (α ⬝ᵥ b) • vecMulVec a β := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem mul_vmv_mul (A B : Matrix (Fin n) (Fin n) k) (w φ : Fin n → k) :
    A * vecMulVec w φ * B = vecMulVec (A *ᵥ w) (φ ᵥ* B) := by
  ext i l
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => by ring

theorem vecMul_vmv (φ a α : Fin n → k) : φ ᵥ* vecMulVec a α = (φ ⬝ᵥ a) • α := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

def tU (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : GL (Fin n) k :=
  ⟨1 + vecMulVec v φ, 1 - vecMulVec v φ,
    by simp only [add_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel⟩

theorem tU_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h).val = 1 + vecMulVec v φ := rfl

theorem tU_inv_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h)⁻¹.val = 1 - vecMulVec v φ := rfl

theorem conj_val (g : GL (Fin n) k) (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) :
    (g * tU v φ h * g⁻¹).val = 1 + vecMulVec (g.val *ᵥ v) (φ ᵥ* (g⁻¹).val) := by
  rw [Units.val_mul, Units.val_mul, tU_val, mul_add, add_mul, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_vmv_mul]

theorem tU_mem_unip (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) (hl : ∀ i l : Fin n, l.val ≤ i.val → v i * φ l = 0) :
    tU v φ h ∈ unip k n := by
  refine ⟨fun i l (hli : l.val < i.val) => ?_, fun i => ?_⟩
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i l hli.le, one_apply_ne (fun e => by rw [e] at hli; omega), add_zero]
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i i le_rfl, one_apply_eq, add_zero]

theorem transvection_eq (i j : Fin n) (c : k) :
    transvection i j c = 1 + vecMulVec (Pi.single i c) (Pi.single j 1) := by
  unfold transvection
  congr 1
  ext p q
  simp only [single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem sdot (p q : Fin n) (x : k) (h : q ≠ p) : Pi.single q 1 ⬝ᵥ Pi.single p x = 0 := by
  rw [single_dotProduct, Pi.single_apply, if_neg h, mul_zero]

theorem comm_a (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) :
    (tU (Pi.single pm (1 : k)) (Pi.single p0 1) (sdot _ _ _ h0m))⁻¹ *
      (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm) * tU (Pi.single pm 1) (Pi.single p0 1) (sdot _ _ _ h0m) *
        (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm))⁻¹) =
      tU (Pi.single pm (-1)) (Pi.single p1 1) (sdot _ _ _ h1m) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem comm_b (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) (a b : k) :
    tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm) * tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m) *
      (tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm))⁻¹ * (tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m))⁻¹ =
      tU (Pi.single p0 (a * b)) (Pi.single p1 1) (sdot _ _ _ h01.symm) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all [mul_comm]

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

theorem entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  intro k _ hk n r hr hrn H b hU h2 h3 h4 a c ha hc
  classical
  by_contra hne
  have ofVal : ∀ (g h : GL (Fin n) k), g ∈ H → g.val = h.val → h ∈ H := fun g h hg e => (Units.ext e) ▸ hg
  have H4 : ∀ i j : Fin n, i.val + 1 = j.val → j.val < r →
      (∀ x : k, ∃ hx, tU (Pi.single i x) (Pi.single j 1) hx ∈ H) → False := by
    intro i j hij hj hall
    obtain ⟨x, h, hh, hn⟩ := h4 i j hij hj
    obtain ⟨hx, hm⟩ := hall x
    exact hn (ofVal _ _ hm (by rw [tU_val, hh, transvection_eq]))
  let φ : Fin n → k := fun l => b.val a l
  have hrow : φ ᵥ* (b⁻¹).val = Pi.single a 1 := by
    have e : φ = Pi.single a 1 ᵥ* b.val := by
      ext l
      simp [φ, vecMul, single_dotProduct]
    rw [e, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have H3 : ∀ w (hw : φ ⬝ᵥ w = 0), tU w φ hw ∈ H := fun w hw =>
    h3 _ a (b.val *ᵥ w) ha hw (by rw [conj_val, hrow]; rfl)
  let S := Finset.univ.filter (fun l : Fin n => φ l ≠ 0)
  have hcS : c ∈ S := by simp [S, φ, hne]
  set j := S.min' ⟨c, hcS⟩ with hjdef
  have hjc : j ≤ c := Finset.min'_le S c hcS
  have hφj : φ j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S ⟨c, hcS⟩)).2
  have hlow : ∀ l, l < j → φ l = 0 := fun l hl => by
    by_contra h'
    exact absurd (Finset.min'_le S l (by simp [S, h'])) (not_le.mpr hl)
  obtain ⟨t, ht⟩ := hk.mul_inv_cancel hφj
  have hjr : j.val < r := lt_of_le_of_lt (show j.val ≤ c.val from hjc) hc
  let ψ : Fin n → k := fun l => if j < l then φ l * t else 0
  have hψ : ψ ⬝ᵥ Pi.single j 1 = 0 := by simp [ψ, dotProduct_single]
  have hu : tU (Pi.single j 1) ψ hψ ∈ unip k n := tU_mem_unip _ _ _ (fun i l hli => by
    simp only [Pi.single_apply, ψ]
    split_ifs with h1 h2 <;> first | (simp; done) | (have := Fin.lt_def.mp h2; rw [h1] at hli; omega))
  have hvec : φ ᵥ* ((tU (Pi.single j 1) ψ hψ)⁻¹).val = Pi.single j (φ j) := by
    rw [tU_inv_val, vecMul_sub, vecMul_one, vecMul_vmv, dotProduct_single, mul_one]
    ext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ψ, Pi.single_apply]
    rcases lt_trichotomy l j with hl | hl | hl
    · rw [if_neg (not_lt.mpr hl.le), if_neg hl.ne, hlow l hl]; ring
    · rw [hl]; simp
    · rw [if_pos hl, if_neg hl.ne']; linear_combination (-(φ l)) * ht
  have KEY : ∀ (v : Fin n → k) (hv : Pi.single j 1 ⬝ᵥ v = 0), tU v (Pi.single j 1) hv ∈ H := by
    intro v hv
    have hw : φ ⬝ᵥ (t • (((tU (Pi.single j 1) ψ hψ)⁻¹).val *ᵥ v)) = 0 := by
      rw [dotProduct_smul, dotProduct_mulVec, hvec, single_dotProduct]
      rw [single_dotProduct, one_mul] at hv
      rw [hv, mul_zero, smul_zero]
    refine ofVal _ _ (hU _ hu _ (H3 _ hw)) ?_
    rw [conj_val, hvec, mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, tU_val]
    congr 1
    ext p q
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · linear_combination (v p) * ht
    · simp
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have hn3 : 3 ≤ n := by omega
    let m0 : Fin n := ⟨n - 1, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hm0j : j ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0] at this
      omega
    have hi1j : j ≠ i1 := fun e => by
      have := congrArg Fin.val e
      simp [i1] at this
      omega
    have hm0i1 : i1 ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0, i1] at this
      omega
    have hX := KEY (Pi.single m0 1) (sdot _ _ _ hm0j)
    have hu1 : tU (Pi.single j 1) (Pi.single i1 1) (sdot _ _ _ hi1j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [i1] at hpq; omega))
    have hQ : tU (Pi.single m0 (-1)) (Pi.single i1 1) (sdot _ _ _ hm0i1) ∈ H := by
      have := H.mul_mem (H.inv_mem hX) (hU _ hu1 _ hX)
      exact (congrArg (· ∈ H) (comm_a (k := k) j i1 m0 hi1j hm0j hm0i1)).mp this
    refine H4 j i1 (by simp [i1, hj0]) (by simp [i1]; omega) (fun x => ⟨sdot _ _ _ hi1j.symm, ?_⟩)
    have hP : tU (Pi.single j (-x)) (Pi.single m0 1) (sdot _ _ _ hm0j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [m0] at hpq; omega))
    have hZ := H.mul_mem (hU _ hP _ hQ) (H.inv_mem hQ)
    exact ofVal _ _ hZ ((congrArg Units.val (comm_b j i1 m0 hi1j hm0j hm0i1 (-x) (-1))).trans
      (by rw [tU_val, tU_val, neg_mul_neg, mul_one]))
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have hij : j ≠ i := fun e => by
      have := congrArg Fin.val e
      simp [i] at this
      omega
    exact H4 i j (by simp [i]; omega) hjr (fun x => ⟨sdot _ _ _ hij, KEY _ _⟩)

end GlobalTheory.PosAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PrimRay

theorem eq_of_toReal_eq_smul : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  intro X _ x y d hd hx hy h
  have hx0 : x ≠ 0 := fun h0 => by
    have := hx 0 0 (by simp [h0])
    simp at this
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy 0 0 (by simp [h0])
    simp at this
  obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x y d hd hy0 h
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  generalize Nat.gcd a b = g at hg hcop0 ha' hb'
  subst ha' hb'
  have hcop : Nat.Coprime a' b' := by
    have := hcop0
    have e1 : g * a' / g = a' := Nat.mul_div_cancel_left a' hg
    have e2 : g * b' / g = b' := Nat.mul_div_cancel_left b' hg
    rwa [e1, e2] at this
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hgz : ((g : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : ∀ p q, (a' : ℤ) * x p q = (b' : ℤ) * y p q := fun p q => by
    have := LinearMap.congr_fun₂ hab p q
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    push_cast at this
    apply mul_left_cancel₀ hgz
    linear_combination this
  set z : LinearMap.BilinForm ℤ X := u • y + w • x with hz
  have hxz : ((b' : ℕ) : ℤ) • z = x := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (-u) * h1 p q + (x p q) * huw
  have hyz : ((a' : ℕ) : ℤ) • z = y := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination w * h1 p q + (y p q) * huw
  have hb1 : b' = 1 := hx b' z hxz
  have ha1 : a' = 1 := hy a' z hyz
  have hxy : x = y := by
    ext p q
    simpa [ha1, hb1] using h1 p q
  refine ⟨hxy, ?_⟩
  subst hxy
  obtain ⟨p, q, hpq⟩ : ∃ p q, x p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (LinearMap.ext₂ hc)
  have := LinearMap.congr_fun₂ h p q
  simp only [toReal_apply, LinearMap.smul_apply, smul_eq_mul] at this
  have hne : (x p q : ℝ) ≠ 0 := by exact_mod_cast hpq
  have := mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  exact this

end GlobalTheory.PrimRay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinatesEvenCharactersFourthPowersAssociat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFourth

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' _ Φ w wL hw hwL hΦ hlev xe ht hc
  obtain ⟨σ, f, hE, hne⟩ := _root_.GlobalTheory.SquareSectionWeightZero.main R hR G hG D A U
  obtain ⟨σ', f', hE', hcorr⟩ := GlobalTheory.T.psi_square_even_terms_correspond_transport R hR G hG D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  exact GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation R hR D D' Φ w hw hΦ xe hc f f' (GlobalTheory.T.uniformisationExpansion_functionalEquation R hR G hG D A U 2 (by norm_num) σ f hE)
    (GlobalTheory.T.uniformisationExpansion_functionalEquation R hR G hG D' A' U' 2 (by norm_num) σ' f' hE') hcorr (GlobalTheory.T.cubicalStructure_square_transport R hR D D' Φ w hw hΦ) hne

end GlobalTheory.PsiFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem spanC_core (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (htie : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ v : (ratDatR R cG kKs hk).WL j, v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j))
    (hinj : ∀ i, Function.Injective (iotaR R i))
    (hhk : ∀ (i : Fin D.R.m) (k : ℕ) (Pl : PlE D.host), 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host Pl → Pl ∉ Sb →
      ∃ α Rr, HkDat R Sb i k Pl α Rr)
    (hRd : HeckeRd R cG kKs hk Sb hL) (hEig : EigAd Y Sb eig) :
    SpanC (ratDatR R cG kKs hk) Sb θ hL eig := by
  intro j hj1 hj2
  classical
  have hjj : ((idxOf D j : Fin D.R.m) : ℕ) + 1 = j := by
    show min (j - 1) (D.R.m - 1) + 1 = j
    omega
  have hsg : ∀ c : D.what₂.LL, D.what₂.embLL c = sg0 D A3.A c := fun c =>
    (congrArg (fun g : D.what₂.LL →+* ℂ => g c) (GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL R)).symm
  let I : Set (ℕ × PlE D.host) := {t | 1 ≤ t.1 ∧ t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb}
  have ex : ∀ t : I, ∃ α Rr, HkDat R Sb (idxOf D j) t.1.1 t.1.2 α Rr := fun t =>
    hhk (idxOf D j) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  choose α Rr hD using ex
  let T' : ℕ × PlE D.host → Module.End ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun t =>
    if h : t ∈ I then hkNorm R (idxOf D j) t.1 t.2 • Formalism.IndefR.Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) (Rr ⟨t, h⟩)
    else 0
  let Part : D.what₂.FT → Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun σ =>
    (D.what₂.isot ((idxOf D j : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y (idxOf D j))
  let s : Set D.what₂.FT := {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}
  have hT : ∀ t ∈ I, ∀ u : Fin (R.nW (idxOf D j)) → D.what₂.LL,
      iotaR R (idxOf D j) (hL j t.1 t.2 u) = T' t (iotaR R (idxOf D j) u) := by
    intro t ht u
    simp only [T', dif_pos ht, LinearMap.smul_apply, iotaR_apply]
    exact hRd j t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) hj1 hj2 (hD ⟨t, ht⟩) u
  have hPa : ∀ σ ∈ s, ∀ t ∈ I, ∀ z ∈ Part σ, T' t z = sg0 D A3.A ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL) • z := by
    rintro σ hσ t ht _ ⟨y, hy, rfl⟩
    simp only [T', dif_pos ht, LinearMap.smul_apply]
    have h1 := hEig (idxOf D j) σ t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) (hD ⟨t, ht⟩) hσ.2 y hy
    have h2 : eig ((idxOf D j : ℕ) + 1) σ t.1 t.2 = eig j σ t.1 t.2 := by rw [hjj]
    rw [h2, hsg] at h1
    exact h1
  have hGa : ∀ u, iotaR R (idxOf D j) u ∈ ⨆ σ ∈ s, Part σ → u ∈ goodL D (ratDatR R cG kKs hk) θ j := by
    intro u hu
    refine (htie j hj1 hj2 u).2 ?_
    have hle : (⨆ σ ∈ s, Part σ) ≤ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) :=
      iSup₂_le fun σ _ => Submodule.map_le_iff_le_comap.2 fun y _ => readW_mem_goodW Y (idxOf D j) y
    exact hle hu
  intro v hv
  have hv' : iotaR R (idxOf D j) v ∈ ⨆ σ ∈ s, Part σ :=
    goodW_le_parts Y hI hG (idxOf D j) j hjj ((htie j hj1 hj2 v).1 hv)
  have hd := _root_.GlobalTheory.descent_joint_eigen (sg0 D A3.A) (iotaR R (idxOf D j)) (goodL D (ratDatR R cG kKs hk) θ j)
    (fun u _ h0 => hinj (idxOf D j) (h0.trans (map_zero _).symm)) (fun t => hL j t.1 t.2) T' I hT Part s
    (fun σ t => ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) hPa hGa v hv'
  have hle : (⨆ σ ∈ s, goodL D (ratDatR R cG kKs hk) θ j ⊓ ⨅ t ∈ I,
      Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) ≤
      ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D (ratDatR R cG kKs hk) θ j ⊓
        ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb),
          Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL) :=
    iSup₂_mono fun σ _ => inf_le_inf_left _ (le_iInf fun k => le_iInf fun Pl => le_iInf fun h =>
      iInf₂_le (f := fun t (_ : t ∈ I) => Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL))
        (k, Pl) h)
  exact hle hd

end Core

end GlobalTheory.EigSpanDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem starOld_cell_mult_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab w ψ' : InvFun (𝓞 E))
    (hDom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X)
    (hφ : IsPolyFan H.bar q φ) (hlab : SimpLab H.bar q φ lab) (M : ℕ) (hM : maxMult H.bar q φ ≤ M)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ')
    (hli' : LinearIndependent ℤ γ') (hp' : ∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X))
    (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγφ : IsCell H.bar φ γ) (hγψ : IsCell H.bar ψ' γ)
    (hw : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0)
    (hin : ∀ j, InRCone γ (γ' j)) :
    ∃ hφ' : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ'.mem i⟩ : balForms H.bar X)) ≤ M ∧
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by

  obtain ⟨m', δ, hδ, hδli, -, hδγ⟩ := hlab.2 X hX m γ hγφ
  obtain ⟨δ₁, hδ₁, hδ₁li, hδ₁p, hδδ₁⟩ := _root_.GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim H.bar φ δ hδ hδli
  have hγδ₁ : ∀ k, InRCone δ₁ (γ k) := fun k => hδδ₁ _ (hδγ k)

  obtain ⟨h₂, h₂n, h₂z, h₂c⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form H.bar φ δ₁ γ hδ₁ hγφ hγδ₁
  obtain ⟨h₁, h₁n, h₁z, h₁c⟩ := _root_.GlobalTheory.PolFan.CellFace.exists_face_form H.bar ψ' γ γ' hγψ hγ' hin
  obtain ⟨h, hn, hz, hc⟩ := _root_.GlobalTheory.PolFan.exists_linForm_cut_face_of_face H.bar δ₁ γ γ' h₂ h₁ hδ₁.mem hδ₁.nonneg hin h₂n h₂z h₂c h₁n h₁z h₁c
  have hin₁ : ∀ j, InRCone δ₁ (γ' j) := fun j => inRCone_trans hγδ₁ (hin j)
  obtain ⟨s, hs, hsf⟩ := _root_.GlobalTheory.PolFan.eq_subfamily_of_face H.bar δ₁ γ' hδ₁.mem hγ'.mem h hδ₁li hli' hδ₁p hp' hin₁ hn hz
    (fun i hi => hc _ (hδ₁.mem i) (hδ₁.nonneg i) (inRCone_self δ₁ i) hi)
  have hγ'eq : γ' = fun j => δ₁ (s j) := funext hs
  have hcut : IsFaceCut δ₁ s h := ⟨hn, hsf⟩
  have hφ' : IsCell H.bar φ γ' := by
    rw [hγ'eq]; exact _root_.GlobalTheory.PolFan.isCell_face_of_isFaceCut E H q φ hφ X hX (hDom X) m' δ₁ hδ₁ _ s h hcut
  refine ⟨hφ', ?_, fun β hβ hβn hβc h1 => ?_⟩
  ·
    have hliB : LinearIndependent ℤ (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) :=
      LinearIndependent.of_comp (balForms H.bar X).subtype hδ₁li
    have hrange : Set.range (fun j => (⟨γ' j, hφ'.mem j⟩ : balForms H.bar X)) ⊆
        Set.range (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨s j, Subtype.ext (hs j).symm⟩
    have hdvd := _root_.GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset (balForms H.bar X) _ _ hliB hrange
    have hpos := _root_.GlobalTheory.PolFan.cellMult_pos H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X))
    have hle := SmoothEnd.cellMult_le_maxMult hX hδ₁ hδ₁li hδ₁p
    have hle' : cellMult H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) ≤ M := by
      exact_mod_cast hle.trans hM
    exact (Nat.le_of_dvd hpos hdvd).trans hle'
  ·
    rw [hw β hβ hβn (inRCone_trans hin hβc)] at h1
    exact zero_ne_one h1

end GlobalTheory.PolFan
end

