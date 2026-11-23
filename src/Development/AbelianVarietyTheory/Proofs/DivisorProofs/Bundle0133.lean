module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtale

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Polynomial

namespace GlobalTheory.UnitaryCongruenceDet

noncomputable section

def ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_eq (x : E) : cc x = ccHom E x := rfl

theorem transpose_mul_mul_map {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γᵀ * G * γ.map (ccHom E) = G := by
  ext i j
  have hs : ∀ k, γ *ᵥ Pi.single k 1 = fun a => γ a k := by
    intro k; funext a; simp [mulVec, dotProduct, Pi.single_apply]
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [herm, cc_eq, hs] at hij
  simp only [Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, hij]
  simp [Pi.single_apply]

theorem det_mul_cc_det {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γ.det * cc γ.det = 1 := by
  have e := congrArg Matrix.det (transpose_mul_mul_map G γ h)
  have hd : (γ.map (ccHom E)).det = ccHom E γ.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, det_transpose, hd] at e
  rw [cc_eq]
  apply mul_right_cancel₀ hG
  linear_combination e

theorem isIntegral_of_left_eigen {r : ℕ} {Ω : Type} [Field Ω] [Algebra E Ω]
    (C : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hC : ∀ x ∈ Λ, C *ᵥ x ∈ Λ)
    (μ : Ω) (u : Fin r → Ω) (hu : u ≠ 0) (hμ : u ᵥ* C.map (algebraMap E Ω) = μ • u) :
    IsIntegral ℤ μ := by
  classical
  let φ := algebraMap E Ω
  let g : (Fin r → E) →ₗ[E] Ω :=
    { toFun := fun x => u ⬝ᵥ (fun a => φ (x a))
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add (f := _)]
        rw [← dotProduct_add]; rfl
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  let N : Submodule ℤ Ω := (Λ.restrictScalars ℤ).map (g.restrictScalars ℤ)
  have hNfg : N.FG := (Submodule.FG.restrictScalars (R := ℤ) hfg).map _
  have hN : N ≠ ⊥ := by
    intro hN
    apply hu
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      intro x hx
      have : g x ∈ N := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [hN, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker] at this
    simpa [g, φ, dotProduct, Pi.single_apply, apply_ite] using this
  refine isIntegral_of_smul_mem_submodule N hN hNfg μ ?_
  rintro n hn
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨C *ᵥ x, hC x hx, ?_⟩
  change u ⬝ᵥ (fun a => φ ((C *ᵥ x) a)) = μ • (u ⬝ᵥ fun a => φ (x a))
  have h1 : (fun a => φ ((C *ᵥ x) a)) = C.map φ *ᵥ (fun a => φ (x a)) := by
    funext a; exact RingHom.map_mulVec φ C x a
  rw [h1, dotProduct_mulVec, hμ, smul_dotProduct, smul_eq_mul]

theorem prod_eq_one_add {Ω : Type} [Field Ω] (M : ℕ) (hM : (M : Ω) ≠ 0) (s : Multiset Ω)
    (hs : ∀ l ∈ s, IsIntegral ℤ ((l - 1) / (M : Ω))) :
    ∃ z : Ω, IsIntegral ℤ z ∧ s.prod = 1 + M * z := by
  have hMint : IsIntegral ℤ (M : Ω) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Ω (M : ℤ)))
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz, hprod⟩ := ih (fun l hl => hs l (Multiset.mem_cons_of_mem hl))
    have ha := hs a (Multiset.mem_cons_self a s)
    set w := (a - 1) / (M : Ω) with hw
    have ha' : a = 1 + M * w := by rw [hw]; field_simp; ring
    refine ⟨w + z + M * w * z, (ha.add hz).add ((hMint.mul ha).mul hz), ?_⟩
    rw [Multiset.prod_cons, hprod, ha']
    ring

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r),
    3 ≤ M →
    (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) →
    ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M X hM hΓ γ hγ
  classical
  obtain ⟨⟨hherm, -⟩, hcong⟩ := (hΓ γ).1 hγ
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ X.Λ, A *ᵥ x ∈ X.Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply isIntegral_of_left_eigen A X.Λ X.Λ_fg X.Λ_span hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hint : IsIntegral ℤ ((g.det - 1) / (M : E)) := by
    have h1 : φ ((g.det - 1) / (M : E)) = z := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφdet]; field_simp; ring
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 (by change IsIntegral ℤ (φ _); rw [h1]; exact hz)
  have hc := det_mul_cc_det X.Gm g X.Gm_det hherm
  by_contra hne
  have hx : (⟨(g.det - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (g.det - 1) / (M : E) = 0 := congrArg Subtype.val h
    rcases div_eq_zero_iff.1 this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hME h
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((g.det - 1) / M)‖ := hσ
  have h1 : ‖σ g.det‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ g.det)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ g.det - 1‖ ≤ 2 := by
    have := norm_sub_le (σ g.det) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

end

end GlobalTheory.UnitaryCongruenceDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbOverSumInjective
section
open NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
  [Field F] [NumberField F] [NumberField.IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def secAlg {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) : A →+* Γ(T, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) : f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst h
  rfl

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.kappa_comm {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.Opens) (a : A) :
    ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
      (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((I.subschemeι ≫ pullback.snd _ g).app U).hom (_root_.GlobalTheory.HilbAff.secAlg A g U a) := by
  have key : (I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B =
      (I.subschemeι ≫ pullback.snd _ g) ≫ g := by
    simp [pullback.condition]
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (_root_.GlobalTheory.HilbAff.str A B).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    have := congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hm : (_root_.GlobalTheory.HilbAff.str A B).appTop ≫
      (I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp) = g.appLE ⊤ U (by simp) ≫ (I.subschemeι ≫ pullback.snd _ g).app U := by
    calc _ = ((I.subschemeι ≫ pullback.fst _ g) ≫ _root_.GlobalTheory.HilbAff.str A B).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = ((I.subschemeι ≫ pullback.snd _ g) ≫ g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) (by simp) :=
          _root_.GlobalTheory.HilbAff.appLE_eq_of_eq key _ _ _ _
      _ = _ := by
        rw [Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) hm

def kappa {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((I.subschemeι ≫ pullback.snd _ g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => kappa_comm A B g I U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem kappa_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    kappa A B g I U (c ⊗ₜ[A] b) = ((I.subschemeι ≫ pullback.snd _ g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤ ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ U) :=
    (((I.subschemeι ≫ pullback.snd _ g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

def xI (C : Type) [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) :
    (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
    (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv).ker

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.basic_iff_kappa {r N : ℕ} (e : Module.Basis (Fin N) A B)
    (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (_root_.GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (hI : _root_.GlobalTheory.HilbAff.Good A B r g I) :
    _root_.GlobalTheory.HilbAff.Basic A B e σ (T := T) ⟨g, ⟨I, hI⟩⟩ ↔ ∀ U : T.affineOpens,
      letI := (_root_.GlobalTheory.HilbAff.secAlg A g U).toAlgebra;
      Function.Bijective fun c : Fin r → Γ(T, U) =>
        _root_.GlobalTheory.HilbAff.kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k)) := by
  unfold _root_.GlobalTheory.HilbAff.Basic
  refine forall_congr' fun U => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, _root_.GlobalTheory.HilbAff.kappa_tmul]

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_res {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) {U V : T.Opens}
    (h : U ≤ V) : (T.presheaf.map (homOfLE h).op).hom.comp (_root_.GlobalTheory.HilbAff.secAlg A g V) =
      _root_.GlobalTheory.HilbAff.secAlg A g U := by
  ext a
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op)

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.secAlg_comp {C : Type} [CommRing C] {T : Scheme.{0}}
    (h : T ⟶ Spec (CommRingCat.of C)) (f : A →+* C) (U : T.Opens) :
    _root_.GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom f)) U =
      (_root_.GlobalTheory.HilbAff.secAlg C h U).comp f := by
  have hm : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (h ≫ Spec.map (CommRingCat.ofHom f)).appLE ⊤ U (by simp) =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) :=
    calc _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop ≫ h.appLE ⊤ U (by simp) :=
          congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h _ ⊤ U _)
      _ = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Spec.map (CommRingCat.ofHom f)).appTop) ≫ h.appLE ⊤ U (by simp) :=
          (Category.assoc _ _ _).symm
      _ = (CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv) ≫
          h.appLE ⊤ U (by simp) := by rw [← Scheme.ΓSpecIso_inv_naturality]
      _ = _ := Category.assoc _ _ _
  ext a
  exact congrArg (fun φ => φ.hom a) hm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] in
theorem _root_.GlobalTheory.HilbAff.eq_of_secAlg_top {T : Scheme.{0}}
    {g₁ g₂ : T ⟶ Spec (CommRingCat.of A)}
    (h : _root_.GlobalTheory.HilbAff.secAlg A g₁ ⊤ = _root_.GlobalTheory.HilbAff.secAlg A g₂ ⊤) :
    g₁ = g₂ := by
  apply ext_of_isAffine
  have e₁ : g₁.appLE ⊤ ⊤ le_top = g₁.appTop := g₁.appLE_eq_app
  have e₂ : g₂.appLE ⊤ ⊤ le_top = g₂.appTop := g₂.appLE_eq_app
  have h' : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₁.appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g₂.appLE ⊤ ⊤ le_top := CommRingCat.hom_ext h
  rw [e₁, e₂] at h'
  exact (cancel_epi _).1 h'

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImageStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_adjoin_baseChange_image' : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S) (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) (S' : Subalgebra R S), A₀ ≤ S' → ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))) (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))), Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  first | exact @GlobalTheory.etale_adjoin_baseChange_image | exact GlobalTheory.etale_adjoin_baseChange_image | (intros; apply GlobalTheory.etale_adjoin_baseChange_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDifferentials
section
open scoped TensorProduct Polynomial

namespace GlobalTheory.EtaleCoordRank

open KaehlerDifferential TensorProduct

theorem finrank_and_linearIndependent_D_unit_mul : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  intro R B K _ _ _ _ _ d t h
  have key : ∃ b : Module.Basis (Fin d) B Ω[B⁄R], ∀ i, b i = D R B (t i) := by
    letI : Algebra (MvPolynomial (Fin d) R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
    haveI : IsScalarTower R (MvPolynomial (Fin d) R) B :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change algebraMap R B r = MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.C r)
        simp
    haveI : Algebra.Etale (MvPolynomial (Fin d) R) B := h
    obtain ⟨⟨b, hb⟩, _⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B (Fin d)
    refine ⟨b, fun i => ?_⟩
    rw [hb]
    congr 1
    change MvPolynomial.eval₂Hom (algebraMap R B) t (MvPolynomial.X i) = t i
    simp
  obtain ⟨b, hb⟩ := key
  let b' : Module.Basis (Fin d) K (K ⊗[B] Ω[B⁄R]) := b.baseChange K
  refine ⟨by rw [Module.finrank_eq_card_basis b', Fintype.card_fin], ?_⟩
  intro ι e u ht
  have hli : LinearIndependent K (fun i => b' (e i)) := b'.linearIndependent.comp e e.injective
  have hfun : (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) =
      (fun i => Units.map (algebraMap B K : B →* K) (u i)) • (fun i => b' (e i)) := by
    funext i
    simp only [Pi.smul_apply', Units.smul_def, Units.coe_map, MonoidHom.coe_coe, b',
      Module.Basis.baseChange_apply, hb]
    rw [Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, ← algebraMap_smul K (u i : B),
      ← algebraMap_smul K (t (e i)), ht, zero_smul, add_zero]
  rw [hfun]
  exact hli.units_smul _

end GlobalTheory.EtaleCoordRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfieldStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_hom_to_field_factors_algClosed_subfield : ∀ (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L] (α : A →+* K) (ι : K →+* L) (β : B →+* L), (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α → ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  first | (exact @GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (exact GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield) | (intros; apply GlobalTheory.etale_hom_to_field_lands_in_algClosed_subfield  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegralStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_tensor : ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  first | (exact @GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (exact GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral) | (intros; apply GlobalTheory.etale_integralClosure_tensor_of_etale_of_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtaleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_prod_of_etale : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  first | (exact @GlobalTheory.etale_prod) | (exact GlobalTheory.etale_prod) | (intros; apply GlobalTheory.etale_prod <;> assumption)
end

