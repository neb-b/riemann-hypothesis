module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField
open scoped nonZeroDivisors

section

variable (E : Type) [Field E] [NumberField E]

theorem mem_dual_one_iff_span_dualInt (y : E) :
    y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.span ℤ (Set.range (dualInt E)) := by
  classical
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  have h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [h2, ← Submodule.restrictScalars_mem ℤ, h]
  have : (⇑(integralBasis E).traceDual) = dualInt E := by
    funext k
    unfold dualInt Module.Basis.traceDual
    congr!
  rw [this]

theorem different_mul_dual_one :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀
    (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]

theorem exists_different_mul_dualInt (x : 𝓞 E) (hx : x ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ z : 𝓞 E, (z : E) = (x : E) * dualInt E k := by
  have h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hx
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [different_mul_dual_one, FractionalIdeal.mem_one_iff] at h3
  exact h3

end

theorem different_generator_dualInt :
    ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E]
      [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) →
      (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) →
      Submodule.span A {algebraMap A K d} =
        Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} →
      algebraMap A K d ≠ 0 ∧
        (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧
        ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
          ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  intro A K _ _ _ _ E _ _ σ d _ hσ hd
  have key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
      ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
    set M : Submodule A K :=
      Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM
    have hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), mul_add]; exact M.add_mem ha hb
      | smul n a _ ha =>
        rw [map_zsmul, mul_smul_comm]
        exact zsmul_mem ha n
    have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [different_mul_dual_one]
      exact FractionalIdeal.one_mem_one _
    have h2 : σ 1 ∈ M := by
      refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_
      · intro x hx y hy'
        obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        have hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
          rw [hd]; exact Submodule.subset_span ⟨x, hx0, rfl⟩
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
        change σ ((x : E) * y) ∈ M
        rw [map_mul, ← ha, smul_mul_assoc]
        exact M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))
      · intro x y hx hy
        rw [map_add (f := _)]; exact M.add_mem hx hy
    rw [map_one, hM, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, by simpa only [Algebra.smul_def] using hu⟩
  refine ⟨?_, ?_, key⟩
  · intro h0
    obtain ⟨u, hu⟩ := key
    simp [h0] at hu
  · intro k
    have hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        y * σ (dualInt E k) ∈ (algebraMap A K).range := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        obtain ⟨z, hz⟩ := exists_different_mul_dualInt E x hx k
        rw [← map_mul, ← hz]
        exact hσ z
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul n a _ ha =>
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem ⟨n, rfl⟩ ha
    exact hy _ (hd ▸ Submodule.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem linearIndependent_span_of_dual_unit :
    ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ)
      (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V),
      IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) →
      LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  intro V _ L _ _ n b u f N hN hf
  classical

  let U : Matrix (Fin n) (Fin n) V := Matrix.of fun i k => b.repr (u i) k
  let F : Matrix (Fin n) (Fin n) V := Matrix.of fun k j => f j (b k)
  have hUF : U * F = N • (1 : Matrix (Fin n) (Fin n) V) := by
    ext i j
    have h1 : f j (u i) = ∑ k, b.repr (u i) k * f j (b k) := by
      calc f j (u i) = f j (∑ k, b.repr (u i) k • b k) := by rw [b.sum_repr]
        _ = ∑ k, b.repr (u i) k * f j (b k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.mul_apply, U, F, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← h1, hf]
    split_ifs <;> simp
  have hdet : IsUnit U.det := by
    have h2 : U.det * F.det = N ^ n := by
      rw [← Matrix.det_mul, hUF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact isUnit_of_mul_isUnit_left (h2 ▸ hN.pow n)
  have hb : b.toMatrix u = U.transpose := by
    ext k i
    simp [Module.Basis.toMatrix_apply, U]
  have hdet' : IsUnit (b.toMatrix u).det := by
    rw [hb, Matrix.det_transpose]; exact hdet
  have hdet2 : IsUnit (b.det u) := by
    rw [Module.Basis.det_apply]; exact hdet'
  exact (Module.Basis.is_basis_iff_det b).mpr hdet2

end GlobalTheory.CompanionTheory.CommAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsDiffGenerator
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem diffGen_v_le_one {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (a : 𝓞 E) : v (σ (a : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral v.integer (σ (a : E)) := h1.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

theorem diffGen_exists_max {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (D : Ideal (𝓞 E)) :
    ∃ x₀ ∈ D, ∀ x ∈ D, v (σ ((x : 𝓞 E) : E)) ≤ v (σ ((x₀ : 𝓞 E) : E)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian D : D.FG)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨0, D.zero_mem, fun x hx => ?_⟩
    rw [← hs, h, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨x₀, hx₀s, hmax⟩ := s.exists_max_image (fun g : 𝓞 E => v (σ (g : E))) h
    refine ⟨x₀, ?_, fun x hx => ?_⟩
    · rw [← hs]
      exact Submodule.subset_span hx₀s
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      calc v (σ ((y + z : 𝓞 E) : E)) = v (σ (y : E) + σ (z : E)) := by simp
        _ ≤ max (v (σ (y : E))) (v (σ (z : E))) := v.map_add _ _
        _ ≤ _ := max_le hy hz
    | smul r y _ hy =>
      calc v (σ ((r • y : 𝓞 E) : E)) = v (σ (r : E)) * v (σ (y : E)) := by simp [smul_eq_mul]
        _ ≤ 1 * v (σ (x₀ : E)) := mul_le_mul' (diffGen_v_le_one v σ r) hy
        _ = _ := one_mul _

theorem exists_diff_generator (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (E : Type) [Field E] [NumberField E]
    (σ : E →+* C) :
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) ∧
      ∃ d : O, algebraMap O C d ≠ 0 ∧ v (algebraMap O C d) = diffAbs v σ ∧
        Submodule.span O {algebraMap O C d} =
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have hint : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range := by
    intro a
    have h1 : IsIntegral ℤ (σ (a : E)) := (a.isIntegral_coe).map σ.toIntAlgHom
    have h3 : σ (a : E) ∈ v.integer := hv.mem_of_integral (h1.tower_top (A := O))
    exact RingHom.mem_range.2 (hv.exists_of_le_one ((Valuation.mem_integer_iff v _).1 h3))
  refine ⟨hint, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := diffGen_exists_max v σ (differentIdeal ℤ (𝓞 E))
  obtain ⟨d, hd⟩ := RingHom.mem_range.1 (hint x₀)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσz : σ (z : E) ≠ 0 := (map_ne_zero σ).2 (by simpa using hz0)
  have hx0ne : σ (x₀ : E) ≠ 0 := by
    intro h
    have hle := hmax z hz
    rw [h, map_zero] at hle
    exact (v.ne_zero_iff.2 hσz) (le_antisymm hle zero_le)
  refine ⟨d, by rw [hd]; exact hx0ne, ?_, ?_⟩
  · rw [hd, diffAbs]
    apply le_antisymm
    · exact le_ciSup (f := fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E)))
        ⟨v (σ (x₀ : E)), by rintro _ ⟨x, rfl⟩; exact hmax x x.2⟩ ⟨x₀, hx₀⟩
    · exact ciSup_le fun x => hmax x x.2
  · rw [hd]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      have hle : v (σ (x : E) / σ (x₀ : E)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax x hx) zero_le
      obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, hc, div_mul_cancel₀ _ hx0ne]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FgInfRestrictScalarsOfIntegers
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem fg_inf_restrictScalars_of_integers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type)
    [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V) (hL : L.FG) :
    (L ⊓ U.restrictScalars O).FG := by
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let f : L →ₗ[O] (V ⧸ U) := (U.mkQ.restrictScalars O).comp L.subtype
  haveI : Module.Finite O L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite O (LinearMap.range f) := inferInstance
  haveI : Module.Flat O (LinearMap.range f) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hx⟩ ⟨⟨a, ha⟩, h⟩
    have h1 : a • x = 0 := congrArg Subtype.val h
    have ha0 : algebraMap O C a ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero ha (hinj (by simpa using h0))
    rw [← algebraMap_smul C a x] at h1
    have : x = 0 := (smul_eq_zero.1 h1).resolve_left ha0
    simp [this]
  haveI : Module.Free O (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  let p : L →ₗ[O] V := L.subtype.comp (LinearMap.id - s.comp f.rangeRestrict)
  have key : L ⊓ U.restrictScalars O = LinearMap.range p := by
    apply le_antisymm
    · rintro x ⟨hxL, hxU⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      have : f.rangeRestrict ⟨x, hxL⟩ = 0 := by
        apply Subtype.ext
        change U.mkQ x = 0
        exact (Submodule.Quotient.mk_eq_zero U).2 hxU
      simp [p, this]
    · rintro _ ⟨y, rfl⟩
      refine ⟨(y - s (f.rangeRestrict y)).2, ?_⟩
      have h2 : f.rangeRestrict (s (f.rangeRestrict y)) = f.rangeRestrict y :=
        LinearMap.congr_fun hs _
      have h3 : f (y - s (f.rangeRestrict y)) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val h2).symm
      exact (Submodule.Quotient.mk_eq_zero U).1 h3
  rw [key]
  exact Module.Finite.iff_fg.1 inferInstance

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotient
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal

theorem exists_colength_one (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A]
    (χ : A →ₐ[k] k) (e : A) (J : Ideal A) (he : IsIdempotentElem e) (hχ : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) (hJe : J ≤ Ideal.span {e}) (hJ0 : J ≠ ⊥) :
    ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧
      (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧
      (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  classical
  set m := RingHom.ker χ with hm
  have hfix : ∀ a ∈ J, e * a = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp (hJe ha)
    calc e * (x * e) = x * (e * e) := by ring
      _ = x * e := by rw [he.eq]
  have hJ : ¬ J ≤ m * J := by
    intro hle
    have hfg : (J : Submodule A A).FG := IsNoetherian.noetherian J
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])
    apply hJ0
    rw [eq_bot_iff]
    intro a ha
    have hs : 1 - r ∈ m := by
      have := m.neg_mem hr
      rwa [neg_sub] at this
    have hsa : (1 - r) * a = a := by
      have h0 : r * a = 0 := by simpa [smul_eq_mul] using hr0 a ha
      rw [sub_mul, one_mul, h0, sub_zero]
    have hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (e * (1 - r)) ^ (n + 1) * a = (e * (1 - r)) ^ n * (e * ((1 - r) * a)) := by ring
          _ = a := by rw [hsa, hfix a ha, ih]
    obtain ⟨n, hn⟩ := hnil (1 - r) hs
    rw [Ideal.mem_bot, ← hpow n, hn, zero_mul]
  obtain ⟨t, htJ, htW⟩ := SetLike.not_le_iff_exists.mp hJ
  let W : Submodule k A := (m * J).restrictScalars k
  have hq : W.mkQ t ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htW
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)
  set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl
  have hlt : l t = 1 := by
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  have hlW : ∀ a ∈ m * J, l a = 0 := by
    intro a ha
    have : W.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]
  have hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m := by
    intro r
    rw [hm, RingHom.mem_ker]
    simp
  let J₁ : Ideal A :=
    { carrier := {a | a ∈ J ∧ l a = 0}
      add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨J.zero_mem, map_zero l⟩
      smul_mem' := fun c a ha => by
        refine ⟨J.mul_mem_left c ha.1, ?_⟩
        have hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a := by
          rw [Algebra.smul_def]
          ring
        change l (c * a) = 0
        rw [hsplit, map_add (f := _), map_smul, ha.2, smul_zero, zero_add]
        exact hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }
  have hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0 := fun a => Iff.rfl
  refine ⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩
    have := ((hmemJ₁ t).mp h).2
    rw [hlt] at this
    exact one_ne_zero this
  · intro a ha
    refine ⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩
    rw [← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]
  · intro a ha
    exact (hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩
  · intro a ha
    exact ((hmemJ₁ a).mp ha).2

end GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂] (r r₂ : ℕ) (L : AddSubgroup E) (C C' : AddSubgroup E₂) (Δ : AddSubgroup (E × E₂)), LocFree R r L → LocFree R r₂ C → LocFree R r₂ C' → (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → (∀ v w, (v, w) ∈ Δ → v ∈ L ∧ w ∈ C) → (∀ v ∈ L, ∃ w, (v, w) ∈ Δ) → (∀ w, (0, w) ∈ Δ ↔ w ∈ C') → (∀ w ∈ C, ∃ v, (v, w) ∈ Δ) → LocFree R (r + r₂) Δ ∧ LocFree R r (Δ.comap (AddMonoidHom.inl E E₂)) := by
  intro o Ω _ _ _ R E E₂ _ _ _ _ r r₂ L C C' Δ hL hC hC' hsm hsub hliftL hker hliftC
  have hC'eq : AddSubgroup.comap (LinearMap.inr Ω E E₂).toAddMonoidHom Δ = C' := by
    ext w
    change (0, w) ∈ Δ ↔ w ∈ C'
    exact hker w
  have hLeq : AddSubgroup.map (LinearMap.fst Ω E E₂).toAddMonoidHom Δ = L := by
    ext v
    constructor
    · rintro ⟨⟨v', w⟩, h, rfl⟩
      exact (hsub v' w h).1
    · intro hv
      obtain ⟨w, hw⟩ := hliftL v hv
      exact ⟨(v, w), hw, rfl⟩
  have hCeq : AddSubgroup.map (LinearMap.snd Ω E E₂).toAddMonoidHom Δ = C := by
    ext w
    constructor
    · rintro ⟨⟨v, w'⟩, h, rfl⟩
      exact (hsub v w' h).2
    · intro hw
      obtain ⟨v, hv⟩ := hliftC w hw
      exact ⟨(v, w), hv, rfl⟩
  have hΔ : LocFree R (r + r₂) Δ := by
    have h := GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt.main R (LinearMap.inr Ω E E₂) (LinearMap.fst Ω E E₂)
      LinearMap.inr_injective LinearMap.fst_surjective
      (LinearMap.range_inr (R := Ω) (M := E) (M₂ := E₂)) Δ r₂ r hsm
      (by rw [hC'eq]; exact hC') (by rw [hLeq]; exact hL)
    rwa [Nat.add_comm] at h
  refine ⟨hΔ, ?_⟩
  have h := _root_.GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main R (LinearMap.inl Ω E E₂) (LinearMap.snd Ω E E₂)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl (R := Ω) (M := E) (M₂ := E₂)) Δ r r₂ hΔ (by rw [hCeq]; exact hC)
  have he : (LinearMap.inl Ω E E₂).toAddMonoidHom = AddMonoidHom.inl E E₂ := by
    ext x <;> simp
  rw [he] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHolds
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem kernel_graph_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) :=
  @PositivityTheory.Xgn.kernel_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

