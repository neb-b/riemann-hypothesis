module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLDiagonalBlocks
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.ShinBlock

open GlobalTheory.Shin

variable {K : Type} [Field K]

theorem tl_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    tl a M = M.submatrix (Fin.castAdd b) (Fin.castAdd b) := by
  ext i j
  simp only [tl, ent, Matrix.submatrix_apply]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem br_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    br a b M = M.submatrix (Fin.natAdd a) (Fin.natAdd a) := by
  ext i j
  simp only [br, ent, Matrix.submatrix_apply]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem inPar_mul {a n : ℕ} {x y : GL (Fin n) K} (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) := by
  intro i j hj hi
  rw [Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : (k : ℕ) < a
  · rw [hx i k hk hi, zero_mul]
  · rw [hy k j hj (by omega), mul_zero]

theorem inPar_one {a n : ℕ} : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h; subst h; omega

theorem inPar_inv {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) : InPar a x⁻¹ := by
  have hB : Matrix.BlockTriangular (x : Matrix (Fin n) (Fin n) K)
      (fun i : Fin n => if a ≤ (i : ℕ) then 1 else 0) := by
    intro i j hij
    simp only at hij
    split_ifs at hij with h1 h2 <;> first | omega | exact hx i j (by omega) (by omega)
  haveI : Invertible (x : Matrix (Fin n) (Fin n) K) := x.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hB
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact this (by simp only; rw [if_pos hi, if_neg (by omega)]; exact Nat.zero_lt_one)

theorem tl_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hy : InPar a y) :
    tl a (x * y).val = tl a x.val * tl a y.val := by
  rw [tl_eq, tl_eq, tl_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin b, x.val (Fin.castAdd b i) (Fin.natAdd a k) *
      y.val (Fin.natAdd a k) (Fin.castAdd b j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hy _ _ (by simp) (by simp), mul_zero]
  rw [this, add_zero]

theorem br_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) :
    br a b (x * y).val = br a b x.val * br a b y.val := by
  rw [br_eq, br_eq, br_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin a, x.val (Fin.natAdd a i) (Fin.castAdd b k) *
      y.val (Fin.castAdd b k) (Fin.natAdd a j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hx _ _ (by simp) (by simp), zero_mul]
  rw [this, zero_add]

theorem tl_one {a b : ℕ} : tl a (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [tl_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.castAdd_injective a b)

theorem br_one {a b : ℕ} : br a b (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [br_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.natAdd_injective b a)

theorem isUnit_tl {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (tl a x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := tl a x⁻¹.val)
  rw [← tl_mul (inPar_inv hx), mul_inv_cancel, tl_one]

theorem isUnit_br {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (br a b x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := br a b x⁻¹.val)
  rw [← br_mul hx, mul_inv_cancel, br_one]

theorem coe_tlG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (tlG a x).val = tl a x.val := by
  unfold tlG toG
  rw [dite_eq_left (isUnit_tl hx)]
  rfl

theorem coe_brG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (brG a b x).val = br a b x.val := by
  unfold brG toG
  rw [dite_eq_left (isUnit_br hx)]
  rfl

theorem gal_val {K' : Type} [Field K'] (t : K →+* K') {n : ℕ} (x : GL (Fin n) K) :
    (gal t n x).val = x.val.map t := rfl

theorem inPar_gal {K' : Type} [Field K'] (t : K →+* K') {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi
  rw [gal_val, Matrix.map_apply, hx i j hj hi, map_zero]

theorem tl_map {K' : Type} [Field K'] (t : K →+* K') (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j
  simp only [tl, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem br_map {K' : Type} [Field K'] (t : K →+* K') (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j
  simp only [br, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem tlG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    tlG a (gal t (a + b) x) = gal t a (tlG a x) := by
  ext1
  rw [coe_tlG (inPar_gal t hx), gal_val, gal_val, coe_tlG hx, tl_map]

theorem brG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    brG a b (gal t (a + b) x) = gal t b (brG a b x) := by
  ext1
  rw [coe_brG (inPar_gal t hx), gal_val, gal_val, coe_brG hx, br_map]

theorem tlG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    tlG a (x * y) = tlG a x * tlG a y := by
  ext1
  rw [coe_tlG (inPar_mul hx hy), tl_mul hy, Units.val_mul, coe_tlG hx, coe_tlG hy]

theorem brG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    brG a b (x * y) = brG a b x * brG a b y := by
  ext1
  rw [coe_brG (inPar_mul hx hy), br_mul hx, Units.val_mul, coe_brG hx, coe_brG hy]

theorem tlG_one {a b : ℕ} : tlG a (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_tlG inPar_one, tl_one, Units.val_one]

theorem brG_one {a b : ℕ} : brG a b (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_brG inPar_one, br_one, Units.val_one]

theorem prod_blocks {a b : ℕ} (l : List (GL (Fin (a + b)) K)) (hl : ∀ x ∈ l, InPar a x) :
    InPar a l.prod ∧ tlG a l.prod = (l.map (tlG a)).prod ∧ brG a b l.prod = (l.map (brG a b)).prod := by
  induction l with
  | nil => exact ⟨inPar_one, tlG_one, brG_one⟩
  | cons x l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    have hx := hl x List.mem_cons_self
    simp only [List.prod_cons, List.map_cons]
    exact ⟨inPar_mul hx h1, by rw [tlG_mul hx h1, h2], by rw [brG_mul hx h1, h3]⟩

theorem nrm_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b →
    ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ →
    nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  intro F F' _ _ _ _ s _ a b n hn γ δ hγ hδ h
  subst hn
  have hall : ∀ x ∈ (List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ), InPar a x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact inPar_gal _ hδ
  obtain ⟨-, h2, h3⟩ := prod_blocks _ hall
  have hn : nrm s δ = ((List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ)).prod := rfl
  refine ⟨?_, ?_⟩
  · have e : nrm s (tlG a δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (tlG a)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (tlG_gal _ hδ).symm
    rw [e, ← h2, ← hn, h]
    exact tlG_gal _ hγ
  · have e : nrm s (brG a b δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (brG a b)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (brG_gal _ hδ).symm
    rw [e, ← h3, ← hn, h]
    exact brG_gal _ hγ

end GlobalTheory.ShinBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapCompAlgebraMap
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GenFibMap

variable {A A' A'' X X' X'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [CommRing X]
  [CommRing X'] [CommRing X''] [Algebra A X] [Algebra A' X'] [Algebra A'' X'']

theorem submonoid_le (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P') (nonZeroDivisors A')).comap
        (Localization.localRingHom P P' χ hP) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨φ a, hφ a ha, ?_⟩
  simp only [IsScalarTower.algebraMap_apply A X (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply A' X' (Localization.AtPrime P'),
    Localization.localRingHom_to_map, hc]

def genFibMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P') :=
  IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
    (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P')) (Localization.localRingHom P P' χ hP)
    (submonoid_le φ χ hc hφ P P' hP)

theorem genFibMap_comp_algebraMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    (genFibMap φ χ hc hφ P P' hP).comp
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))) =
      (algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))).comp
        (Localization.localRingHom P P' χ hP) :=
  IsLocalization.map_comp _

theorem genFibMap_apply (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) (y : X) :
    genFibMap φ χ hc hφ P P' hP
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
          (algebraMap X (Localization.AtPrime P) y)) =
      algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))
          (algebraMap X' (Localization.AtPrime P') (χ y)) := by
  rw [genFibMap, IsLocalization.map_eq, Localization.localRingHom_to_map]

theorem ext {C : Type} [CommRing C] (P : Ideal X) [P.IsPrime]
    {u v : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* C}
    (h : ∀ y : X, u (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y)) =
      v (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y))) : u = v := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A))
  apply IsLocalization.ringHom_ext P.primeCompl
  exact RingHom.ext h

theorem genFibMap_comp (φ₁ : A →+* A') (χ₁ : X →+* X')
    (hc₁ : ∀ a, χ₁ (algebraMap A X a) = algebraMap A' X' (φ₁ a))
    (hφ₁ : ∀ a ∈ nonZeroDivisors A, φ₁ a ∈ nonZeroDivisors A')
    (φ₂ : A' →+* A'') (χ₂ : X' →+* X'')
    (hc₂ : ∀ a, χ₂ (algebraMap A' X' a) = algebraMap A'' X'' (φ₂ a))
    (hφ₂ : ∀ a ∈ nonZeroDivisors A', φ₂ a ∈ nonZeroDivisors A'')
    (φ₃ : A →+* A'') (χ₃ : X →+* X'')
    (hc₃ : ∀ a, χ₃ (algebraMap A X a) = algebraMap A'' X'' (φ₃ a))
    (hφ₃ : ∀ a ∈ nonZeroDivisors A, φ₃ a ∈ nonZeroDivisors A'')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (P'' : Ideal X'') [P''.IsPrime]
    (h₁ : P = P'.comap χ₁) (h₂ : P' = P''.comap χ₂) (h₃ : P = P''.comap χ₃)
    (hχ : ∀ y, χ₃ y = χ₂ (χ₁ y)) :
    (genFibMap φ₂ χ₂ hc₂ hφ₂ P' P'' h₂).comp (genFibMap φ₁ χ₁ hc₁ hφ₁ P P' h₁) =
      genFibMap φ₃ χ₃ hc₃ hφ₃ P P'' h₃ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.comp_apply, genFibMap_apply, hχ]

theorem genFibMap_id (φ : A →+* A) (χ : X →+* X)
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A X (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A)
    (P : Ideal X) [P.IsPrime] (hP : P = P.comap χ) (hχ : ∀ y, χ y = y) :
    genFibMap φ χ hc hφ P P hP = RingHom.id _ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.id_apply, genFibMap_apply, hχ]

end GlobalTheory.GenFibMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernel
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_ker : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  intro T _ _ ι _ _ 𝒜 hA hcov E _ _ Q _ Ek _ _ e h he hh heh hinj hsurj g hg f hf k x hx
  classical

  set L := Localization.AtPrime (Q.comap (e k)) with hL
  obtain ⟨⟨z, a'⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid L (nonZeroDivisors (𝒜 k))) x
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap (e k)).primeCompl z
  dsimp only at hx ⊢
  set G := GlobalTheory.LocAcyc.GenFib (𝒜 k) L
  set X := IsLocalization.mk' G (IsLocalization.mk' L y s) a' with hX
  set v : G := algebraMap L G (a' : L) * algebraMap L G (algebraMap (Ek k) L (s : Ek k)) with hv
  have hvu : IsUnit v := by
    refine (IsLocalization.map_units G a').mul ?_
    exact (IsLocalization.map_units L s).map _
  have hXv : X * v = algebraMap L G (algebraMap (Ek k) L y) := by
    rw [hv, ← mul_assoc, hX, IsLocalization.mk'_spec, ← map_mul, IsLocalization.mk'_spec]

  have hgy : g k (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [← hXv, map_mul, hx, zero_mul]
  rw [hg] at hgy

  obtain ⟨⟨m0, hm0⟩, hm0y⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) _ _).1 hgy
  obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.1 hm0
  simp only at hm0y
  rw [IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q), ← map_mul] at hm0y
  obtain ⟨⟨u, hu⟩, huy⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).1 hm0y
  simp only at huy
  obtain ⟨m, u', rfl⟩ := hsurj u
  obtain ⟨m', htm'⟩ := hcov t
  obtain ⟨l1, hkl1, hml1⟩ := directed_of (· ≤ ·) k m
  obtain ⟨l, hl1, hm'l⟩ := directed_of (· ≤ ·) l1 m'
  have hkl : k ≤ l := hkl1.trans hl1
  have hml : m ≤ l := hml1.trans hl1
  let c : 𝒜 l := ⟨t, hA hm'l htm'⟩
  have hc0 : c ∈ nonZeroDivisors (𝒜 l) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have : (t : T) = 0 := congrArg Subtype.val h0
    exact nonZeroDivisors.ne_zero ht this
  have hprod : h m l hml u' * (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    apply hinj l
    rw [map_mul, map_mul, heh, heh, he, map_zero]
    simpa [mul_assoc] using huy
  have hu'' : h m l hml u' ∈ (Q.comap (e l)).primeCompl := by
    change e l (h m l hml u') ∉ Q
    rw [heh]; exact hu
  set Ll := Localization.AtPrime (Q.comap (e l))
  have h1 : algebraMap (Ek l) Ll (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    have := congrArg (algebraMap (Ek l) Ll) hprod
    rw [map_mul, map_zero] at this
    exact ((IsLocalization.map_units Ll ⟨_, hu''⟩).mul_right_eq_zero).1 this
  have h2 : algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) (algebraMap (Ek l) Ll (h k l hkl y)) = 0 := by
    have hcm : algebraMap (𝒜 l) Ll c ∈ Algebra.algebraMapSubmonoid Ll (nonZeroDivisors (𝒜 l)) :=
      Submonoid.mem_map.2 ⟨c, hc0, rfl⟩
    have := congrArg (algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll)) h1
    rw [map_mul, map_zero, ← IsScalarTower.algebraMap_apply, map_mul] at this
    exact ((IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) ⟨_, hcm⟩).mul_right_eq_zero).1 this
  refine ⟨l, hkl, ?_⟩
  have hfy : f k l hkl (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [hf]; exact h2
  have := congrArg (f k l hkl) hXv
  rw [map_mul, hfy] at this
  exact ((hvu.map (f k l hkl)).mul_left_eq_zero).1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteType
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by
  intro R B _ _ _ h P _ K _ _ _ _ hfg
  haveI : Algebra.EssFiniteType P.ResidueField K := IntermediateField.fg_top_iff.mp hfg
  haveI : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R P.ResidueField K
  haveI hr : IsRegularRing (B ⊗[R] K) := h K
  exact ⟨inferInstance, fun Q _ => hr.isRegularLocalRing_localization Q⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

open MeasureTheory

def hTransAB (a b : ℕ) (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a * ((starRingEnd ℂ) ((t : ℂ) + (y : ℂ) * I))⁻¹ ^ b *
    ((‖(t : ℂ) + (y : ℂ) * I‖ : ℝ) : ℂ) ^ (-2 * σ) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

theorem hTransAB_two_zero (σ : ℂ) (ν y : ℝ) : hTransAB 2 0 σ ν y = hTrans σ ν y := by
  unfold hTransAB hTrans phi
  congr 1; funext t
  simp only [pow_zero, mul_one]

variable {F : Type} [Field F] [NumberField F]

def termQ (σ : ℂ) (b ν : F) (q : Emb F → ℕ) (z : Emb F → ℂ) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    iteratedDeriv (q τ) (hTrans σ (τ ν)) (τ b * (z τ).im))

theorem termQ_zero (σ : ℂ) (b ν : F) (z : Emb F → ℂ) : termQ σ b ν 0 z = fTerm σ z b ν := by
  unfold termQ fTerm
  simp only [Pi.zero_apply, iteratedDeriv_zero]

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumGaussianConvolutionSeriesTermIntegralStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.ConvSeries.hasSum_term_integral | exact GlobalTheory.ConvSeries.hasSum_term_integral | (intros; apply GlobalTheory.ConvSeries.hasSum_term_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuousStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous : ∀ {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ), Continuous N → N 0 = 1 → (∀ s t, N (s + t) = N s * N t) → ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | exact GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | (intros; apply GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter <;> assumption)
end

