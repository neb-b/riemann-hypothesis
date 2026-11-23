module

public import Mathlib
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import GroundTheory.LocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
section
noncomputable section

open Polynomial Formalism.UG

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL_of {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {x : L} (hx : x ∈ intL L) :
    σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]; exact hx

def sigO (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  σ.restrict (intL L) (intL L) fun _ hx => mem_intL_of hσ hx

def piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : intL L :=
  ⟨ϖ, by
    change Valued.v ϖ ≤ 1
    rw [h.2.2.2.1]
    exact_mod_cast (WithZero.coe_le_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1))⟩

@[simp] theorem coe_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : ((piO h : intL L) : L) = ϖ := rfl

def unitFil {R : Type} [CommRing R] (I : Ideal R) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : Rˣ) : R) - 1 = (a : R) * ((b : R) - 1) + ((a : R) - 1) := by push_cast; ring
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e]; exact I.add_mem (I.mul_mem_left _ hb) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : Rˣ) : R) - 1 = -((a⁻¹ : Rˣ) : R) * ((a : R) - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [e]; exact I.mul_mem_left _ ha

theorem mem_unitFil {R : Type} [CommRing R] {I : Ideal R} {u : Rˣ} : u ∈ unitFil I ↔ (u : R) - 1 ∈ I := Iff.rfl

def piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Ideal (AdjoinRoot P.1) :=
  Ideal.span {algebraMap (intL L) (AdjoinRoot P.1) (piO h) ^ m}

def filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (m : ℕ) :
    Subgroup (AdjoinRoot P.1)ˣ :=
  unitFil (piPow h P m)

theorem mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)} {m : ℕ}
    {u : (AdjoinRoot P.1)ˣ} : u ∈ filt h P m ↔ (u : AdjoinRoot P.1) - 1 ∈ piPow h P m := Iff.rfl

theorem piPow_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (piPow h P) := fun a b hab => by
  unfold piPow
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow _ hab

theorem filt_antitone {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    Antitone (filt h P) := fun a b hab _ hu => piPow_antitone h P hab hu

theorem filt_zero {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) :
    filt h P 0 = ⊤ := by
  ext u; simp [filt, mem_unitFil, piPow]

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem piO_mem_of_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {M : Ideal (intL L)}
    (hM : M.IsMaximal) : piO h ∈ M := by
  by_contra hϖ
  obtain ⟨y, i, hi, e⟩ := hM.exists_inv hϖ
  have hlt : Valued.v ((y : L) * ϖ) < 1 := by
    rw [map_mul, h.2.2.2.1]
    have hy : Valued.v (y : L) ≤ 1 := y.2
    calc Valued.v (y : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
        ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
  have hi1 : (i : L) = 1 - (y : L) * ϖ := by
    have := congrArg Subtype.val e
    simp only [Subring.coe_add, Subring.coe_mul, coe_piO, OneMemClass.coe_one] at this
    linear_combination this
  have hv : Valued.v (i : L) = 1 := by rw [hi1]; exact Valuation.map_one_sub_of_lt _ hlt
  have hi0 : (i : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  have hinv : (i : L)⁻¹ ∈ intL L := by
    change Valued.v ((i : L)⁻¹) ≤ 1
    rw [map_inv₀, hv, inv_one]
  have hu : IsUnit i := isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hi0])⟩
  exact hM.ne_top (M.eq_top_of_isUnit_mem hi hu)

theorem isUnit_one_add_piO_mul {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) (a : AdjoinRoot P.1) :
    IsUnit (1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a) := by
  by_contra hn
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  letI : Module.Finite (intL L) (AdjoinRoot P.1) := .of_basis (AdjoinRoot.powerBasis' P.2.1).basis
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap (intL L) (AdjoinRoot P.1))
    (RingHom.IsIntegral.of_finite (RingHom.finite_algebraMap.mpr inferInstance)) M
  have hϖ : algebraMap (intL L) (AdjoinRoot P.1) (piO h) ∈ M := piO_mem_of_isMaximal h hmax
  have h1 : 1 + algebraMap (intL L) (AdjoinRoot P.1) (piO h) * a ∈ M := hxM (Ideal.mem_span_singleton_self _)
  have : (1 : AdjoinRoot P.1) ∈ M := by
    have := M.sub_mem h1 (M.mul_mem_right a hϖ)
    simpa using this
  exact hM.ne_top ((Ideal.eq_top_iff_one M).2 this)

theorem isUnit_of_sub_one_mem {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (s := sigO σ h.2.1)) {m : ℕ} (hm : 1 ≤ m) {x : AdjoinRoot P.1} (hx : x - 1 ∈ piPow h P m) :
    IsUnit x := by
  have hx1 : x - 1 ∈ piPow h P 1 := piPow_antitone h P hm hx
  unfold piPow at hx1
  rw [pow_one, Ideal.mem_span_singleton'] at hx1
  obtain ⟨a, ha⟩ := hx1
  have := isUnit_one_add_piO_mul h P a
  rwa [mul_comm, ha, add_sub_cancel] at this

end GlobalTheory.NormEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

theorem span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [PiLp.single_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [PiLp.single_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp [hcoef]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem isZLattice_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)],
    IsZLattice ℝ (latOf N) := by
  intro F _ _ _ N hN _
  refine ⟨?_⟩
  rw [eq_top_iff, ← span_range_remb F, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc : ∃ c ∈ N, c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩
  obtain ⟨c, hcN, hc0⟩ := hc
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ ℚ (L := F) {a / c}
  let α : 𝓞 F := ⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩
  have hmem : (y : F) * a ∈ N := by
    have h := Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN
    have he : α • c = (y : F) * a := by
      rw [Algebra.smul_def]
      show (y • (a / c)) * c = (y : F) * a
      rw [zsmul_eq_mul]
      field_simp
    rw [he] at h
    exact h
  have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a) := by
    ext τ
    simp only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))

end GlobalTheory.LipschitzTR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdelicSL2
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_ideal_eq_of_span_of_linearIndependent
    (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ}
    (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)) (h12 : J₁ ≤ J₂)
    (hspan : Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤)
    (hli : LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k))) :
    J₁ = J₂ := by
  refine le_antisymm h12 (fun t ht => ?_)
  have hmem : Ideal.Quotient.mk J₁ t ∈ Submodule.span R
      (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  set s : R ⊗[A] B := ∑ k, c k • ((1 : R) ⊗ₜ[A] v k) with hs
  have hmk : ∀ (J : Ideal (R ⊗[A] B)), Ideal.Quotient.mk J s
      = ∑ k, c k • Ideal.Quotient.mk J ((1 : R) ⊗ₜ[A] v k) := by
    intro J
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have h1 : t - s ∈ J₁ := by
    rw [← Ideal.Quotient.eq, hmk J₁, hc]
  have h2 : s ∈ J₂ := by
    have := J₂.sub_mem ht (h12 h1)
    simpa using this
  have hsum : ∑ k, c k • Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k) = 0 := by
    rw [← hmk J₂, Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hc0 : ∀ k, c k = 0 := Fintype.linearIndependent_iff.1 hli c hsum
  have hs0 : s = 0 := by simp [hs, hc0]
  rw [hs0, sub_zero] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerWedgeFormMapEqSmulOfBasis
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem theta_comm {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => theta_comm A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra;
    theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
      ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (x : letI := (secAlg A g U).toAlgebra; Γ(T, U) ⊗[A] B) :
    kappa A B g I U x =
      (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x) := by
  letI := (secAlg A g U).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hk : kappa A B g I U (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
          ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) :=
        (((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hk, theta_tmul, map_mul]
    congr 1
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    rw [← e]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl

theorem ker_kappa_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    RingHom.ker (kappa A B g I U) =
      Ideal.comap (theta A B g U) (RingHom.ker (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom) := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, kappa_apply_eq]; exact Iff.rfl

def psi (C : Type) [CommRing C] [Algebra A C] :
    C ⊗[A] B →+* Γ(pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))), ⊤) :=
  (pullbackSpecIso A B C).hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom.comp
      (Algebra.TensorProduct.comm A C B).toRingHom)

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestric
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_res_apply (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    {U V : T.Opens} (h : U ≤ V) :
    letI := (secAlg A g U).toAlgebra
    letI := (secAlg A g V).toAlgebra
    ∀ (ρ : Γ(T, V) →ₐ[A] Γ(T, U)), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom →
    ∀ t : Γ(T, V) ⊗[A] B,
      kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (kappa A B g I V t) := by
  letI := (secAlg A g U).toAlgebra
  letI := (secAlg A g V).toAlgebra
  intro ρ hρ t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
    have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := by
      rw [← hρ]; rfl
    rw [hc]
    congr 1
    · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
      rfl
    · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
          (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
          (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
      exact (congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm

theorem kappa_res (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (U V : T.affineOpens) (h : (U : T.Opens) ≤ V) :
    letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
    letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
    ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
      (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤ RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        change _ = GlobalTheory.HilbAff.secAlg A g U a
        rw [← GlobalTheory.HilbAff.secAlg_res A g h]; rfl }
  refine ⟨ρ, rfl, ?_⟩
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [GlobalTheory.HilbAff.kappa_res_apply A B g I h ρ rfl t, ht, map_zero]

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijectiveStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  first | exact @GlobalTheory.KummerTorsor.bijective | exact GlobalTheory.KummerTorsor.bijective | (intros; apply GlobalTheory.KummerTorsor.bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushoutStatement
section
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' : ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'), IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'), ((letI := qa'.hom.toAlgebra; p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔ (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first | (exact @GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (exact GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (intros; apply GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout  <;> assumption)
end

