module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAll
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInClosureLocalization
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isIntegrallyClosedIn_closure_localization : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  letI := closureAlg A R D
  let M : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    exact hinj (h.trans (map_zero _).symm)
  haveI : IsDomain (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : IsIntegrallyClosed (GlobalTheory.LocAcyc.GenFib A R) :=
    isIntegrallyClosed_of_isLocalization (GlobalTheory.LocAcyc.GenFib A R) M hM
  have hRGF : Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) :=
    IsLocalization.injective (GlobalTheory.LocAcyc.GenFib A R) hM
  have h1 : IsIntegrallyClosedIn D (D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R)) :=
    GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
  obtain ⟨hDinj, hDcl⟩ := isIntegrallyClosedIn_iff.mp h1
  let g : closure A R D →+* D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R) :=
    (algebraMap D _).comp (closure A R D).subtype
  have hg : Function.Injective g := hDinj.comp Subtype.val_injective
  have hunit : ∀ n : Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R), IsUnit (g n) := by
    rintro ⟨_, s, hs, rfl⟩
    have hs0 : algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hs (hRGF (h.trans (map_zero _).symm))
    have hL : IsUnit (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
        (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) :=
      ((IsFractionRing.injective (GlobalTheory.LocAcyc.GenFib A R) _).ne_iff' (map_zero _)).mpr hs0 |>.isUnit
    have heq : g (algebraMap R (closure A R D) s) = Algebra.TensorProduct.includeRight
        (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
          (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) := by
      rw [Algebra.TensorProduct.includeRight.commutes]
      rfl
    rw [heq]
    exact hL.map _
  let φ := IsLocalization.lift (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
    (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) hunit
  have hφ : φ.comp (algebraMap (closure A R D) _) = g := IsLocalization.lift_comp _

  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) z
    have hc : g c = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
        (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) (hg := hunit) c 0 n).mp hz
      rw [mul_zero] at this
      exact this
    have : c = 0 := hg (hc.trans (map_zero g).symm)
    simp only [this, IsLocalization.mk'_zero]
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx => ?_⟩
  · intro a b hab
    apply hg
    rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, hab]
  · obtain ⟨p, hp, hpx⟩ := hx
    have hev : Polynomial.eval₂ g (φ x) p = 0 := by
      have := Polynomial.hom_eval₂ p (algebraMap (closure A R D) _) φ x
      rw [hpx, map_zero, hφ] at this
      exact this.symm
    have hxD : IsIntegral D (φ x) := by
      refine ⟨p.map (closure A R D).subtype, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hev
    obtain ⟨d, hd⟩ := hDcl hxD

    have hdC : Polynomial.eval₂ (closure A R D).subtype d p = 0 := by
      apply hDinj
      rw [Polynomial.hom_eval₂, hd, map_zero]
      exact hev
    have hdmem : d ∈ closure A R D := by
      letI : Algebra R D := (baseHom A R D).toAlgebra
      letI : Algebra (closure A R D) D := (closure A R D).subtype.toAlgebra
      haveI : IsScalarTower R (closure A R D) D := .of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsIntegral R (closure A R D) := ⟨fun c => by
        let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
        exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2⟩
      have hxC : IsIntegral (closure A R D) d := ⟨p, hp, hdC⟩
      exact isIntegral_trans _ hxC
    refine ⟨⟨d, hdmem⟩, hφinj ?_⟩
    rw [← RingHom.comp_apply, hφ]
    exact hd

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  first | exact @GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | exact GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | (intros; apply GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChangeStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZModTorsorFiniteProjective_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D] [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  first | (exact @GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (exact GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (intros; apply GlobalTheory.LocAcyc.isZModTorsor_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
section
open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.TorsorColim

def bcAct (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) : G →* (S ⊗[R] A ≃ₐ[S] S ⊗[R] A) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]

@[simp]
theorem bcAct_tmul (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) (g : G) (s : S) (a : A) :
    bcAct S act g (s ⊗ₜ[R] a) = s ⊗ₜ[R] act g a := rfl

def prodMapOf (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    D ⊗[B] D →ₐ[B] (Multiplicative (ZMod q) → D) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))

@[simp]
theorem prodMapOf_tmul (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (x y : D) (g : Multiplicative (ZMod q)) :
    prodMapOf B D q act (x ⊗ₜ[B] y) g = x * act g y := by
  simp [prodMapOf]

theorem eventually_and {J : Type} [Category J] [IsFiltered J] {j : J}
    (P Q : ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f))
    (hQ : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), Q k (f₀ ≫ f)) :
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f) ∧ Q k (f₀ ≫ f) := by
  obtain ⟨k₁, f₁, h₁⟩ := hP
  obtain ⟨k₂, f₂, h₂⟩ := hQ
  let a := IsFiltered.leftToMax k₁ k₂
  let b := IsFiltered.rightToMax k₁ k₂
  let e := IsFiltered.coeqHom (f₁ ≫ a) (f₂ ≫ b)
  have he : (f₁ ≫ a) ≫ e = (f₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (f₁ ≫ a) (f₂ ≫ b), (f₁ ≫ a) ≫ e, fun k f => ⟨?_, ?_⟩⟩
  · have := h₁ k (a ≫ e ≫ f)
    simpa only [Category.assoc] using this
  · have := h₂ k (b ≫ e ≫ f)
    rw [he]
    simpa only [Category.assoc] using this

end GlobalTheory.TorsorColim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacTwistMapSurjective
section
noncomputable section

open GlobalTheory.SmGL (twist twist_apply)

namespace GlobalTheory.TypeTwo.EndTwist

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def twistSubIso (ρ : Representation F G V) (χ : G →* Fˣ) :
    Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => by
    have h := S.toSubmodule.smul_mem ((χ g)⁻¹ : Fˣ).val (S.apply_mem_toSubmodule g hv)
    have h2 : ((χ g)⁻¹ : Fˣ).val • (twist ρ χ g v) = ρ g v := by
      rw [twist_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rwa [h2] at h⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_twist {ρ : Representation F G V} (h : ρ.IsIrreducible) (χ : G →* Fˣ) :
    (twist ρ χ).IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (twistSubIso ρ χ)).1 h

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b V : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [AddCommGroup V] [Module ℂ V]

end Local

section Ends

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

end Ends

end GlobalTheory.TypeTwo.EndTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLDegRegStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_liftL_and_reg_pow : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l → (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) → deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  first | (exact @GlobalTheory.Shin.liftL_deg_reg) | (exact GlobalTheory.Shin.liftL_deg_reg) | (intros; apply GlobalTheory.Shin.liftL_deg_reg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAllStatement
section
open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocMatrix in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_free_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  let inst := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  have hBasis : Nonempty (Module.Basis (Fin (Module.finrank F B)) (cenOrder ℓ F) (locOrder ℓ Λ)) := by
    let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
      ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
    have hsum (c : Fin (Module.finrank F B) → cenOrder ℓ F) :
        ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
          combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
      rw [AddSubmonoidClass.coe_finsetSum, combMap_apply]
      rfl
    have hli : LinearIndependent (cenOrder ℓ F) w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 : combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
        rw [← hsum, hc, map_zero]
        rfl
      exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
      rintro ⟨z, hz⟩ -
      obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
    exact ⟨Module.Basis.mk hli hsp⟩
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  obtain ⟨basis⟩ := hBasis
  exact ⟨Module.Free.of_basis basis, by rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
section
open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocAzumaya Module in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      IsAzumaya (cenOrder ℓ F) (locOrder ℓ Λ) := by
  intro F B _ _ _ _ _ _ _ _ _ Λ hΛ hfin hspan
  classical
  have hlocalBasis : ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B), (∀ i, e i ∈ Λ) →
      ∃ D : ℕ, 0 < D ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ D →
        letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
        ∃ f : Module.Basis ι (cenOrder ℓ F) (locOrder ℓ Λ),
          (∀ i, (f i : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) ∧
          ∀ (y : locOrder ℓ Λ) (b : B), (y : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
            ∀ k, ((f.repr y k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
    intro ι _ e he
    obtain ⟨D, hD, hDint⟩ := exists_den_coords F B Λ hfin ι e
    refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
    let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
    have hco : ∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F :=
      fun x hx k => GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hDint x hx k)
    have hv : ∀ i, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i ∈ locOrder ℓ Λ := fun i => Algebra.subset_adjoin ⟨_, he i, rfl⟩
    let v : ι → locOrder ℓ Λ := fun i => ⟨_, hv i⟩
    have hsmul : ∀ (c : cenOrder ℓ F) (y : locOrder ℓ Λ),
        ((c • y : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * y := fun c y => rfl
    have hsum : ∀ c : ι → cenOrder ℓ F, ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
      intro c
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [hsmul, v]
    have hcoef : ∀ (c : ι → cenOrder ℓ F) (b : B),
        ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b →
        ∀ k, ((c k : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k := by
      intro c b h k
      obtain ⟨π, hπ1, hπ2⟩ := exists_coordProj ℓ F B e k
      have h' := congrArg π h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum, hπ1] at h'
      simp only [hπ2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h'
      exact h'
    have hli : LinearIndependent (cenOrder ℓ F) v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc k
      have h0 : ((∑ i, c i • v i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (0 : B) := by
        rw [hc, TensorProduct.tmul_zero]; rfl
      have := hcoef c 0 h0 k
      apply Subtype.ext
      simpa using this
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range v) := by
      rintro y -
      obtain ⟨c, hc, hy⟩ := exists_coords_of_mem_locOrder ℓ F B Λ ι e he hco y y.2
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
      rw [hsum, hy]
    let f := Basis.mk hli hsp
    have hfv : ∀ i, f i = v i := fun i => Basis.mk_apply hli hsp i
    refine ⟨f, fun i => by rw [hfv], fun y b hy k => ?_⟩
    apply hcoef (fun i => f.repr y i) b _ k
    have hs := f.sum_repr y
    simp only [hfv] at hs
    rw [hs, hy]
  obtain ⟨e, he⟩ := exists_basis_mem (F := F) Λ hspan
  have hδ : IsUnit (structMat e).det :=
    (bijective_iff_isUnit_det e).1 (GroundTheory.Brauer.mulLeftRight_bijective F B)
  obtain ⟨m, hm, hmint⟩ := GlobalTheory.SepModel.exists_nat_integral ({((structMat e).det)⁻¹} : Finset F)
  obtain ⟨D, hD, hbasis⟩ := hlocalBasis _ e he
  refine ⟨D * m, by positivity, fun ℓ _ hℓ => ?_⟩
  let _ := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  obtain ⟨f, hf1, hf2⟩ := hbasis ℓ (fun h => hℓ (Dvd.dvd.mul_right h _))
  have hinv : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((structMat e).det)⁻¹ ∈ cenOrder ℓ F :=
    GlobalTheory.SepModel.tmul_mem_cenOrder ℓ (fun h => hℓ (Dvd.dvd.mul_left h _))
      (hmint _ (Finset.mem_singleton_self _))
  have hent : (cenOrder ℓ F).val.toRingHom.mapMatrix (structMat f) =
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom.mapMatrix
        (structMat e) := by
    ext ⟨k, l⟩ ⟨i, j⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply, structMat_apply]
    apply hf2
    simp only [Subalgebra.coe_mul, hf1, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hdet : (((structMat f).det : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F) =
      (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (structMat e).det := by
    have h1 := RingHom.map_det (cenOrder ℓ F).val.toRingHom (structMat f)
    have h2 := RingHom.map_det
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℚ_[ℓ]) (B := F)).toRingHom (structMat e)
    rw [hent, ← h2] at h1
    simpa using h1
  have hunit : IsUnit (structMat f).det := by
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hdet, Subalgebra.coe_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ hδ.ne_zero, Algebra.TensorProduct.one_def]
  have : Nontrivial B := inferInstance
  have : FaithfulSMul (cenOrder ℓ F) (locOrder ℓ Λ) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h : cenMap ℓ F B a = cenMap ℓ F B b :=
      congrArg (fun x : locOrder ℓ Λ => (x : ℚ_[ℓ] ⊗[ℚ] B)) hab
    exact Subtype.ext (cenMap_injective ℓ F B h)
  have := Module.Projective.of_basis f
  have := Module.Finite.of_basis f
  exact ⟨(bijective_iff_isUnit_det f).2 hunit⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureEquiv
section
open IsLocalRing TensorProduct

namespace GlobalTheory.OffDivisor

theorem etale_localization_of_comap : ∀ (R Q A : Type) [CommRing R] [CommRing Q] [Algebra R Q] [CommRing A] [Algebra R A] (p : Ideal R) [p.IsPrime] (q : Ideal Q) [q.IsPrime], q.comap (algebraMap R Q) = p → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime q) A) := by
  intro R Q A _ _ _ _ _ p _ q _ hpq h
  subst hpq
  letI : Algebra (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) :=
    (Localization.localRingHom _ q (algebraMap R Q) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R Q (Localization.AtPrime q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (q.comap (algebraMap R Q))) (B := Localization.AtPrime q) (A := TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A)
  exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (Localization.AtPrime q) A :
    TensorProduct (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A) ≃ₐ[Localization.AtPrime q] TensorProduct R (Localization.AtPrime q) A))

end GlobalTheory.OffDivisor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVRStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_normalization_rootAdjoin_isDVR : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∃ _ : IsDomain (Localization.AtPrime Q), IsDiscreteValuationRing (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.LocNormDVR.main) | (exact GlobalTheory.LocNormDVR.main) | (intros; apply GlobalTheory.LocNormDVR.main  <;> assumption)
end

