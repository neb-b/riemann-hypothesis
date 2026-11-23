module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0172

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjective
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_surj : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  intro T _ _ ι _ _ 𝒜 hmono hunion E _ _ Q _ Ek _ _ e h he hh hsurj g hg b
  classical
  obtain ⟨⟨z, ⟨m, hm⟩⟩, hb0⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) b
  obtain ⟨c, hc, hcm⟩ := hm
  subst hcm
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hz0⟩ := IsLocalization.mk'_surjective Q.primeCompl z
  simp only at hb0 hz0
  subst hz0
  obtain ⟨k₁, y₁, hy₁⟩ := hsurj x
  obtain ⟨k₂, t₂, ht₂⟩ := hsurj s
  obtain ⟨k₃, hc₃⟩ := hunion c
  obtain ⟨k₁₂, h1, h2⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨k, h12, h3⟩ := directed_of (· ≤ ·) k₁₂ k₃
  have hk1 : k₁ ≤ k := h1.trans h12
  have hk2 : k₂ ≤ k := h2.trans h12
  set y := h k₁ k hk1 y₁
  set t := h k₂ k hk2 t₂
  have hy : e k y = x := by rw [hh, hy₁]
  have ht : e k t = s := by rw [hh, ht₂]
  have htQ : t ∈ (Q.comap (e k)).primeCompl := by
    show t ∉ Q.comap (e k)
    rw [Ideal.mem_comap, ht]; exact hs
  set c' : 𝒜 k := ⟨c, hmono h3 hc₃⟩
  have hc' : c' ∈ nonZeroDivisors (𝒜 k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    apply nonZeroDivisors.ne_zero hc
    have := congrArg (fun a : 𝒜 k => (a : T)) h0
    simpa [c'] using this
  set z' : (Localization.AtPrime (Q.comap (e k))) := IsLocalization.mk' (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  set m' : (Localization.AtPrime (Q.comap (e k))) := algebraMap (𝒜 k) (Localization.AtPrime (Q.comap (e k))) c'
  have hm' : m' ∈ Algebra.algebraMapSubmonoid (Localization.AtPrime (Q.comap (e k))) (nonZeroDivisors (𝒜 k)) := ⟨c', hc', rfl⟩
  refine ⟨k, IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩, ?_⟩
  have hu1 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c)) :=
    IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T))
  have hu2 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) :=
    (IsLocalization.map_units (Localization.AtPrime Q) (⟨s, hs⟩ : Q.primeCompl)).map _
  have hgm : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m') = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) := by
    have hm'e : m' = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) (algebraMap (𝒜 k) (Ek k) c') :=
      IsScalarTower.algebraMap_apply (𝒜 k) (Ek k) (Localization.AtPrime (Q.comap (e k))) c'
    rw [hm'e, hg, he, ← IsScalarTower.algebraMap_apply]
    rfl
  have hgt : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s) := by rw [hg, ht]
  have hgy : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by rw [hg, hy]
  have hz' : z' * algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y :=
    IsLocalization.mk'_spec (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  have hX : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩ * algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m' = algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩
  have hz : IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩ * algebraMap E (Localization.AtPrime Q) s = algebraMap E (Localization.AtPrime Q) x :=
    IsLocalization.mk'_spec (Localization.AtPrime Q) x ⟨s, hs⟩
  have hb : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩)
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) *
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩) :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) _ _
  have e1 : b * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hb0, ← mul_assoc, hb, ← map_mul, hz]
  have e2 : g k (IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩) * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hgm, ← hgt, ← mul_assoc, ← map_mul, hX, ← map_mul, ← map_mul, hz', hgy]
  exact (hu1.mul hu2).mul_left_inj.mp (e2.trans e1.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLComm
section
noncomputable section

namespace GlobalTheory.HCCommF

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

def aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (M.submatrix Fin.revPerm Fin.revPerm).transpose

theorem aflip_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) : aflip M i j = M j.rev i.rev := rfl

theorem aflip_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) F) : aflip (M * N) = aflip N * aflip M := by
  unfold aflip
  rw [← Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

theorem aflip_one {n : ℕ} : aflip (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  unfold aflip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem aflip_aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : aflip (aflip M) = M := by
  ext i j; simp [aflip_apply]

theorem aflip_similar {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ P : Matrix (Fin n) (Fin n) F, IsUnit P ∧ P * M = aflip M * P := by
  obtain ⟨P, hP, h⟩ := GlobalTheory.SimilarTranspose.main F (Fin n) (M.submatrix Fin.revPerm Fin.revPerm)
  let Q : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.revPerm (Equiv.refl _)
  have hQ : IsUnit Q := by
    have : Q * (1 : Matrix (Fin n) (Fin n) F).submatrix (Equiv.refl _) Fin.revPerm = 1 := by
      simp only [Q]
      rw [Matrix.submatrix_mul_equiv, mul_one, Matrix.submatrix_one_equiv]
    exact IsUnit.of_mul_eq_one _ this
  have hQM : Q * M = M.submatrix Fin.revPerm Fin.revPerm * Q := by
    have h1 : Q * M = Q * M.submatrix (Equiv.refl _) (Equiv.refl _) := rfl
    rw [h1]
    simp only [Q]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, one_mul, mul_one]
  refine ⟨P * Q, hP.mul hQ, ?_⟩
  rw [mul_assoc, hQM, ← mul_assoc, h, mul_assoc]
  rfl

def aflipG {n : ℕ} (x : GL (Fin n) F) : GL (Fin n) F where
  val := aflip (x : Matrix (Fin n) (Fin n) F)
  inv := aflip ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  val_inv := by rw [← aflip_mul, Units.inv_mul, aflip_one]
  inv_val := by rw [← aflip_mul, Units.mul_inv, aflip_one]

theorem aflipG_coe {n : ℕ} (x : GL (Fin n) F) :
    ((aflipG x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aflip (x : Matrix (Fin n) (Fin n) F) := rfl

theorem aflipG_mul {n : ℕ} (x y : GL (Fin n) F) : aflipG (x * y) = aflipG y * aflipG x :=
  Units.ext (by simp only [aflipG_coe, Units.val_mul, aflip_mul])

theorem aflipG_inv {n : ℕ} (x : GL (Fin n) F) : aflipG x⁻¹ = (aflipG x)⁻¹ := Units.ext rfl

theorem aflipG_aflipG {n : ℕ} (x : GL (Fin n) F) : aflipG (aflipG x) = x := Units.ext (aflip_aflip _)

def aflipE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F := ⟨aflipG, aflipG, aflipG_aflipG, aflipG_aflipG⟩

theorem aflipG_conj {n : ℕ} (x : GL (Fin n) F) : ∃ p : GL (Fin n) F, aflipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, h⟩ := aflip_similar (x : Matrix (Fin n) (Fin n) F)
  refine ⟨hP.unit, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (by simp only [Units.val_mul, aflipG_coe, IsUnit.unit_spec, h])

theorem toG_coe' {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem cl_conj {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (p x : GL (Fin n) F) :
    α (p * x * p⁻¹) = α x := by
  have := hα x p⁻¹
  rwa [inv_inv] at this

theorem class_aflip {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (M : Matrix (Fin n) (Fin n) F) :
    α (toG (aflip M)) = α (toG M) := by
  by_cases h : IsUnit M
  · obtain ⟨x, rfl⟩ := h
    obtain ⟨p, hp⟩ := aflipG_conj x
    have h1 : toG (aflip (x : Matrix (Fin n) (Fin n) F)) = aflipG x := toG_coe' (aflipG x)
    rw [h1, toG_coe', hp, cl_conj hα]
  · have h' : ¬ IsUnit (aflip M) := by
      rintro ⟨x, hx⟩
      exact h ⟨aflipG x, by rw [aflipG_coe, hx, aflip_aflip]⟩
    unfold toG
    rw [dite_eq_right h, dite_eq_right h']

theorem inPar_aflip {a b : ℕ} (y : GL (Fin (a + b)) F) : InPar b (aflipG y) ↔ InPar a y := by
  constructor
  · intro h i j hj hi
    have := h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
    simpa [aflipG_coe, aflip_apply] using this
  · intro h i j hj hi
    rw [aflipG_coe, aflip_apply]
    exact h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)

theorem tl_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl b (aflip M) = aflip (br a b M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dite_eq_left (by omega), dite_eq_left (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

theorem br_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br b a (aflip M) = aflip (tl a M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dite_eq_left (by omega), dite_eq_left (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

theorem gal_id (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

end GlobalTheory.HCCommF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphism
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HcGal

variable {F F' : Type} [Field F] [Field F']

theorem gal_coe (t : F →+* F') {n : ℕ} (x : GL (Fin n) F) :
    ((gal t n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (x : Matrix (Fin n) (Fin n) F).map t := by
  ext i j; simp [gal]

theorem gal_id {n : ℕ} (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem ent_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem isUnit_map_iff (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map t) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have : (M.map t).det = t M.det := by
    rw [RingHom.map_det]; rfl
  rw [this, _root_.map_ne_zero]

theorem toG_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map t) = gal t n (toG M) := by
  unfold toG
  by_cases h : IsUnit M
  · rw [dite_eq_left h, dite_eq_left ((isUnit_map_iff t M).2 h)]
    apply Units.ext
    rw [gal_coe, IsUnit.unit_spec, IsUnit.unit_spec]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ((isUnit_map_iff t M).1 h')), map_one]

theorem tlG_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (gal t n x) = gal t a (tlG a x) := by
  unfold tlG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [tl, Matrix.map_apply, ent_map]

theorem brG_gal (t : F →+* F') (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (gal t n x) = gal t b (brG a b x) := by
  unfold brG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [br, Matrix.map_apply, ent_map]

theorem inPar_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (gal t n x) ↔ InPar a x := by
  unfold InPar
  simp only [gal_coe, Matrix.map_apply, map_eq_zero]

theorem gal_bijective (t : F ≃+* F') (n : ℕ) : Function.Bijective (gal (t : F →+* F') n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨gal (t.symm : F' →+* F) n, fun x => ?_, fun x => ?_⟩
  · ext i j; simp [gal]
  · ext i j; simp [gal]

theorem hc_gal : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) =
    hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  intro F _ _ t a b n α β x
  unfold hc hcTw
  congr 1
  symm
  refine finsum_eq_of_bijective (gal (t : F →+* F) n) (gal_bijective t n) fun y => ?_
  rw [gal_id, gal_id, ← map_inv, ← map_mul, ← map_mul, tlG_gal, brG_gal]
  simp only [inPar_gal]

end GlobalTheory.Shin.HcGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnit
section
noncomputable section

namespace GlobalTheory.Shin.HcUnit

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

theorem toG_val {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem brG_zero {a : ℕ} (x : GL (Fin a) F) : brG 0 a x = x := by
  have h : br 0 a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [br, ent]
  unfold brG
  rw [h, toG_val]

theorem tlG_self {a : ℕ} (x : GL (Fin a) F) : tlG a x = x := by
  have h : tl a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [tl, ent]
  unfold tlG
  rw [h, toG_val]

theorem inPar_zero {n : ℕ} (x : GL (Fin n) F) : InPar 0 x :=
  fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (x : GL (Fin a) F) : InPar a x :=
  fun i _ _ hi => absurd i.isLt (not_lt.mpr hi)

theorem gal_id {n : ℕ} (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

theorem mean_class {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsCl χ) (x : G) :
    (Nat.card G : ℂ)⁻¹ * ∑ᶠ y : G, χ (y⁻¹ * x * y) = χ x := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h' : ∀ y : G, χ (y⁻¹ * x * y) = χ x := fun y => h x y
  have := Fintype.ofFinite G
  rw [finsum_congr h', finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem card_infinitePlace_eq_f {G : Type} {p : G → Prop} (h : ∀ x, p x) :
    Nat.card {x // p x} = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv h)

theorem main : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α →
    hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  intro F _ _ a α hα
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_zero]
    simp only [gal_id, inPar_zero, ↓reduceIte, brG_zero, one_mul]
    exact mean_class hα x
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_self]
    simp only [gal_id, inPar_self, ↓reduceIte, tlG_self, mul_one]
    exact mean_class hα x

end GlobalTheory.Shin.HcUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFderivAtSchwartzOperatorFirst
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

noncomputable section

open Filter Topology Asymptotics

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sliceCLM_add_eq (x' v : V') (f : 𝓢(V × V', ℂ)) :
    sliceCLM (x' + v) f = sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f) := by
  ext x
  simp [SchwartzMap.compSubConstCLM_apply]

theorem remainder_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (x' : V') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : V', ‖v‖ ≤ 1 → ∀ z : W,
      ‖T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) z‖
        ≤ K * ‖v‖ ^ 2 := by
  let q : Seminorm ℂ 𝓢(V × V', ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp (T.comp (sliceCLM x')).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ W E).continuous_seminorm (0, 0)).comp (T.comp (sliceCLM x')).continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V × V') ℂ) q hq
  choose D hD using fun i : ℕ × ℕ => _root_.GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le f i.1 i.2
  refine ⟨(C : ℝ) * ∑ i ∈ s, |D i|, by positivity, fun v hv z => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f with hg
  have ha : ‖((0 : V), v)‖ = ‖v‖ := by simp [Prod.norm_def]
  have h1 : ‖T (sliceCLM x' g) z‖ ≤ q g := SchwartzMap.norm_le_seminorm ℂ _ _
  have h2 : q g ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := by
    have := hC g
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  have h3 : (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g ≤ (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hDi := hD i ((0 : V), v) (by rw [ha]; exact hv)
    rw [ha] at hDi
    calc schwartzSeminormFamily ℂ (V × V') ℂ i g ≤ D i * ‖v‖ ^ 2 := hDi
      _ ≤ |D i| * ‖v‖ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ (∑ j ∈ s, |D j|) * ‖v‖ ^ 2 := by
          gcongr; exact Finset.single_le_sum (fun j _ => abs_nonneg (D j)) hi
  calc ‖T (sliceCLM x' g) z‖ ≤ q g := h1
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := h2
    _ ≤ (C : ℝ) * ((∑ i ∈ s, |D i|) * ‖v‖ ^ 2) := by gcongr
    _ = (C : ℝ) * (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by ring

theorem opFst_add_decomp (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by
  rw [opFst_apply, sliceCLM_add_eq]
  conv_lhs => rw [show SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f
      = (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f) + f + lineSnd v f by abel]
  simp only [map_add (f := _), SchwartzMap.add_apply]

theorem hasFDerivAt_opFst [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ))
    (y : W) (x' : V') :
    HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')
      + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  have hA : HasFDerivAt (fun q : W × V' => T (sliceCLM x' f) q.1)
      ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')) (y, x') :=
    ((T (sliceCLM x' f)).differentiableAt.hasFDerivAt).comp (y, x') hasFDerivAt_fst
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hA ⊢
  have hcont : Continuous fun z : W => dSndCLM T f (z, x') := by
    rw [continuous_clm_apply]
    intro v
    exact (T (sliceCLM x' (lineSnd v f))).continuous
  have hB : (fun p : W × V' => dSndCLM T f (y + p.1, x') p.2 - dSndCLM T f (y, x') p.2)
      =o[𝓝 0] fun p => p := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun p : W × V' => dSndCLM T f (y + p.1, x')) (𝓝 0) (𝓝 (dSndCLM T f (y, x'))) := by
      have : Tendsto (fun p : W × V' => y + p.1) (𝓝 0) (𝓝 y) := by
        have := (tendsto_const_nhds (x := y)).add ((continuous_fst.tendsto (0 : W × V')))
        simpa using this
      exact (hcont.tendsto y).comp this
    filter_upwards [(Metric.tendsto_nhds.mp ht) c hc] with p hp
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖dSndCLM T f (y + p.1, x') - dSndCLM T f (y, x')‖ * ‖p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖p‖ := by
          gcongr
          · rw [← dist_eq_norm]; exact hp.le
          · exact norm_snd_le p
  obtain ⟨K, hK0, hK⟩ := remainder_bound T f x'
  have hC : (fun p : W × V' =>
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
      =o[𝓝 0] fun p => p := by
    have h1 : (fun p : W × V' =>
        T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
        =O[𝓝 0] fun p : W × V' => ‖p‖ ^ 2 := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨K, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : W × V') one_pos] with p hp
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      calc _ ≤ K * ‖p.2‖ ^ 2 := hK p.2 ((norm_snd_le p).trans hp) _
        _ ≤ K * ‖p‖ ^ 2 := by gcongr; exact norm_snd_le p
        _ = K * ‖‖p‖ ^ 2‖ := by rw [norm_pow, norm_norm]
    exact h1.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine ((hA.add hB).add hC).congr_left (fun p => ?_)
  obtain ⟨w, v⟩ := p
  simp only [Prod.mk_add_mk]
  rw [opFst_add_decomp]
  simp only [opFst_apply, dSndCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  abel

end GlobalTheory.SchwartzFstOp
end
end

