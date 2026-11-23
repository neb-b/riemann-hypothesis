module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphisms
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue


open Limits in
theorem glue_away : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  intro S _ ι s hs Y e he
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ e i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ e j := by
    intro i j
    refine Scheme.Cover.hom_ext (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.openCover _ _ fun k => ?_
    let a : Spec ((pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k) ⟶ pullback (𝒰.f i) (𝒰.f j) :=
      (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.f k
    let T := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover.X k
    let A : CommRingCat.of (Localization.Away (s i)) ⟶ T := Spec.preimage (a ≫ pullback.fst (𝒰.f i) (𝒰.f j))
    let B : CommRingCat.of (Localization.Away (s j)) ⟶ T := Spec.preimage (a ≫ pullback.snd (𝒰.f i) (𝒰.f j))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f i) (𝒰.f j) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s i))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s j))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have key : A.hom.comp (algebraMap S (Localization.Away (s i))) =
        B.hom.comp (algebraMap S (Localization.Away (s j))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hu : IsUnit ((A.hom.comp (algebraMap S (Localization.Away (s i)))) (s i * s j)) := by
      rw [map_mul]
      refine IsUnit.mul ?_ ?_
      · exact (IsLocalization.Away.algebraMap_isUnit (s i)).map A.hom
      · rw [key]; exact (IsLocalization.Away.algebraMap_isUnit (s j)).map B.hom
    let L : Localization.Away (s i * s j) →+* T := IsLocalization.Away.lift (s i * s j) hu
    have hL : L.comp (algebraMap S (Localization.Away (s i * s j))) =
        A.hom.comp (algebraMap S (Localization.Away (s i))) := IsLocalization.Away.lift_comp _ _
    have hLA : L.comp (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) = A.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s i)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) hL
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayRight_eq, this]
    have hLB : L.comp (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) = B.hom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (s j)) (RingHom.ext fun x => ?_)
      have := congrArg (fun f => f x) (hL.trans key)
      simp only [RingHom.comp_apply] at this ⊢
      rw [IsLocalization.Away.awayToAwayLeft_eq, this]
    have hA : Spec.map A = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLA]; rfl
    have hB : Spec.map B = Spec.map (CommRingCat.ofHom L) ≫
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hLB]; rfl
    have h2 : Spec.map A ≫ e i = Spec.map B ≫ e j := by
      rw [hA, hB, Category.assoc, Category.assoc, he i j]
    rw [ea, eb] at h2
    exact (Category.assoc _ _ _).symm.trans (h2.trans (Category.assoc _ _ _))
  exact ⟨𝒰.glueMorphisms e hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 e hf i⟩

end GlobalTheory.SecGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomJet
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SquareLiftLemmas

open CategoryTheory GlobalTheory.AnPer GlobalTheory.AnPer.Charts

def liftSq {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) : TrivSqZeroExt O (Fin g → O) →+* C where
  toFun x := ρ x.fst + ∑ a, ρ (x.snd a) * n a
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, map_add (f := _), add_mul,
      Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have h0 : (∑ a, ρ (x.snd a) * n a) * (∑ b, ρ (y.snd b) * n b) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [mul_mul_mul_comm, hn, mul_zero]
    have h1 : ∀ a, ρ ((x * y).snd a) * n a =
        ρ x.fst * (ρ (y.snd a) * n a) + (ρ (x.snd a) * n a) * ρ y.fst := fun a ↦ by
      have : (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
        simp [TrivSqZeroExt.snd_mul, mul_comm]
      rw [this, map_add (f := _), map_mul, map_mul]; ring
    rw [add_mul, mul_add, mul_add, h0, add_zero, TrivSqZeroExt.fst_mul, map_mul]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

theorem liftSq_apply {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (x : TrivSqZeroExt O (Fin g → O)) :
    liftSq ρ n hn x = ρ x.fst + ∑ a, ρ (x.snd a) * n a := rfl

theorem liftSq_inl {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (h : O) : liftSq ρ n hn (TrivSqZeroExt.inl h) = ρ h := by
  simp [liftSq_apply]

theorem liftSq_sec {g : ℕ} {O C : Type} [CommRing O] [Algebra ℂ O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (D : Fin g → Derivation ℂ O O) (h : O) :
    liftSq ρ n hn (tszeSec D h) = ρ h + ∑ a, ρ (D a h) * n a := by
  rw [liftSq_apply, fst_tszeSec]
  simp only [snd_tszeSec]

theorem exists_hom_jet {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C)
    (hdeg : Hom.deg f₁ = Hom.deg f₂) (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (h : ∀ x : Hol (K.W k), Hom.φ f₂ x = Hom.φ f₁ x + ∑ a, Hom.φ f₁ (dw a x) * n a) :
    ∃ χ : K.jet k ⟶ T, Hom.deg χ = Hom.deg f₁ ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        Hom.φ χ x = Hom.φ f₁ x.fst + ∑ a, Hom.φ f₁ (x.snd a) * n a := by
  let ρ : Hol (K.W k) →+* T.C := (Hom.φ f₁ : (K.triv k).C →+* T.C)
  letI := (K.jet k).alg
  letI := (K.triv k).alg
  let φ : (K.jet k).C →ₐ[Hol F.V] T.C :=
    { liftSq ρ n hn with
      commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }
  have hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x := fun _ ↦ rfl
  have hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ :=
    RingHom.ext fun x ↦ liftSq_inl ρ n hn x
  let χ : K.jet k ⟶ T :=
    { φ := φ
      deg := Hom.deg f₁
      le := Hom.le f₁
      mem := fun c hc ↦ by
        have hc' : TrivSqZeroExt.fst c = 0 := hc
        rw [hφ, liftSq_apply, hc', map_zero, zero_add]
        exact T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)
      close := by rw [hcomp]; exact Hom.close f₁ }
  refine ⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩
  · change liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _
    rw [sh_refl, liftSq_inl]; rfl
  · change liftSq ρ n hn (tszeSec dw c) = _
    refine Eq.trans ?_ (h c).symm
    exact liftSq_sec ρ n hn dw c

end GlobalTheory.SquareLiftLemmas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebra
section
open MvPolynomial

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R]

theorem homogeneousComponent_mul_of_homogeneous_left {S : Type} [CommRing S] {k : ℕ} (n : ℕ)
    {P : MvPolynomial σ S} (hP : P.IsHomogeneous k) (Q : MvPolynomial σ S) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := S)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ S) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (T : MvPolynomial σ S),
      ((DirectSum.decompose (homogeneousSubmodule σ S) T m : homogeneousSubmodule σ S m) :
        MvPolynomial σ S) = homogeneousComponent m T :=
    fun m T => MvPolynomial.decomposition.decompose'_apply T m
  rw [e, e] at h
  exact h

noncomputable def piece (I : Ideal R) (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (((AddMonoidAlgebra.coeff F m : reesAlgebra I) : Polynomial R).coeff e)

variable {I : Ideal R}

@[simp] theorem coeff_piece (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m = (AddMonoidAlgebra.coeff F m).1.coeff e := by
  classical
  simp only [piece, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; rfl

@[simp] theorem piece_zero (e : ℕ) : piece I e (0 : MvPolynomial σ (reesAlgebra I)) = 0 := by
  ext m; simp

@[simp] theorem piece_add (e : ℕ) (F G : MvPolynomial σ (reesAlgebra I)) :
    piece I e (F + G) = piece I e F + piece I e G := by
  ext m; simp

theorem piece_X_mul (e : ℕ) (i : σ) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (X i * F) = X i * piece I e F := by
  classical
  ext m
  rw [coeff_piece, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp

theorem piece_C_mul (e : ℕ) (r : reesAlgebra I) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (C r * F) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, C ((r : Polynomial R).coeff p.1) * piece I p.2 F := by
  ext m
  simp [coeff_sum, coeff_C_mul, Polynomial.coeff_mul]

theorem piece_isHomogeneous (e : ℕ) {d : ℕ} {F : MvPolynomial σ (reesAlgebra I)}
    (hF : F.IsHomogeneous d) : (piece I e F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro h
  apply hm
  rw [coeff_piece, h]
  simp

theorem coeff_piece_mem (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m ∈ I ^ e := by
  rw [coeff_piece]
  exact (mem_reesAlgebra_iff I _).1 (AddMonoidAlgebra.coeff F m).2 e

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R] {I : Ideal R}

theorem C_mul_mem_of_pow (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    ∀ (k : ℕ) (b : R), b ∈ I ^ k → ∀ (l t : ℕ) (P : MvPolynomial σ R), P.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff P m ∈ I ^ l) → P ∈ J l → C b * P ∈ J (l + k) := by
  intro k
  induction k with
  | zero =>
    intro b _ l t P _ _ hP
    simpa using (J l).mul_mem_left (C b) hP
  | succ k ih =>
    intro b hb l t P hPh hPc hP
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      have h1 := ih x hx l t P hPh hPc hP
      have h2 : ∀ m, AddMonoidAlgebra.coeff (C x * P) m ∈ I ^ (l + k) := by
        intro m
        rw [coeff_C_mul, pow_add, mul_comm (I ^ l)]
        exact Ideal.mul_mem_mul hx (hPc m)
      have h3 := H (l + k) t y (C x * P) hy (hPh.C_mul x) h2 h1
      rw [show C (x * y) * P = C y * (C x * P) by rw [C_mul]; ring]
      simpa [add_assoc] using h3
    · intro x y hx hy
      rw [C_add, add_mul]
      exact add_mem hx hy

def reesIdeal (I : Ideal R) (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    Ideal (MvPolynomial σ (reesAlgebra I)) where
  carrier := {F | ∀ d e, piece I e (homogeneousComponent d F) ∈ J e}
  zero_mem' := by intro d e; simp
  add_mem' := by
    intro F G hF hG d e
    rw [map_add (f := _), piece_add]
    exact add_mem (hF d e) (hG d e)
  smul_mem' := by
    intro c F hF
    rw [smul_eq_mul]
    revert F
    induction c using MvPolynomial.induction_on with
    | C r =>
      intro F hF d e
      rw [homogeneousComponent_C_mul, piece_C_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      have hpe : p.2 + p.1 = e := by rw [add_comm]; exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [← hpe]
      exact C_mul_mem_of_pow J H p.1 _ ((mem_reesAlgebra_iff I _).1 r.2 p.1) p.2 d _
        (piece_isHomogeneous p.2 (homogeneousComponent_isHomogeneous d F))
        (coeff_piece_mem p.2 _) (hF d p.2)
    | add p q hp hq =>
      intro F hF d e
      rw [add_mul, map_add (f := _), piece_add]
      exact add_mem (hp hF d e) (hq hF d e)
    | mul_X p i hp =>
      intro F hF
      rw [mul_assoc]
      apply hp
      intro d e
      rw [homogeneousComponent_mul_of_homogeneous_left d (isHomogeneous_X _ i)]
      split_ifs
      · rw [piece_X_mul]
        exact (J e).mul_mem_left _ (hF _ e)
      · simp

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

theorem exists_homogeneous_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G ∈ J e) := by
  intro R _ I n J H
  refine ⟨reesIdeal I J H, ?_, ?_⟩
  · intro F hF d d' e
    show piece I e (homogeneousComponent d' (homogeneousComponent d F)) ∈ J e
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d F)]
    split_ifs
    · exact hF d e
    · simp
  · intro t F hFt
    have hG : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R),
        (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G = piece I e F := by
      intro e G hG
      ext m
      rw [hG, coeff_piece]
    constructor
    · intro hF e G hGc
      rw [hG e G hGc]
      have := hF t e
      rwa [homogeneousComponent_eq_self hFt] at this
    · intro h d e
      show piece I e (homogeneousComponent d F) ∈ J e
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule t F).2 hFt)]
      split_ifs
      · exact h e _ fun m => coeff_piece e F m
      · simp

end GlobalTheory.ReesHomogeneous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamily
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ClopenIdealSheaf

theorem map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring

theorem map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

end GlobalTheory.ClopenIdealSheaf

namespace GlobalTheory.ClopenIdealSheaf

theorem exists_idealSheafData_of_isClopen : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W →
    ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  intro Z W hW F hF
  let W' : Z.Opens := ⟨W, hW.isOpen⟩
  let Wc : Z.Opens := ⟨Wᶜ, hW.isClosed.isOpen_compl⟩
  have hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W') := by
    intro U
    obtain ⟨e, -, he, -⟩ := GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z)
      (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc)
      (by
        rw [← inf_sup_left]
        have : W' ⊔ Wc = ⊤ := by
          ext x; simp [W', Wc, em]
        rw [this, inf_top_eq])
      (by
        refine Disjoint.mono inf_le_right inf_le_right ?_
        rw [disjoint_iff]; ext x; simp [W', Wc])
    rw [← he]; exact U.2.basicOpen e
  let V : Z.affineOpens → Z.affineOpens := fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩
  have hVU : ∀ U, (V U : Z.Opens) ≤ U := fun U => inf_le_left
  have hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W := fun U => Set.inter_subset_right
  let I : ∀ U : Z.affineOpens, Ideal Γ(Z, U) := fun U =>
    (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom
  refine ⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩
  · intro U f
    have hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) =
        V (Z.affineBasicOpen f) := by
      apply Subtype.ext
      change Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'
      rw [Scheme.basicOpen_res]
      have := Z.basicOpen_le f
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
      · exact le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left
    exact map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))
  · intro U hU
    have key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A,
        (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A := by
      rintro A B rfl hle
      have : homOfLE hle = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
      exact Ideal.comap_id _
    exact key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)
  · intro x hx
    by_contra hxW
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl
    replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    have hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥ := by
      ext y
      simp only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
        Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun h => hUW h.1 h.2
    haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    have htop : F (V ⟨U, hU⟩) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]
      exact zero_mem _
    have hI : I ⟨U, hU⟩ = ⊤ := by
      simp only [I, htop, Ideal.comap_top]
    change x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx
    rw [hI, Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)

end GlobalTheory.ClopenIdealSheaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLeStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  first | exact @GlobalTheory.SubLen.exists_relLen_of_smul_le | exact GlobalTheory.SubLen.exists_relLen_of_smul_le | (intros; apply GlobalTheory.SubLen.exists_relLen_of_smul_le <;> assumption)
end

