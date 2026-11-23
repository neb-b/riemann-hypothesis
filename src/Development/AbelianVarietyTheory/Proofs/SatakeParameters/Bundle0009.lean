module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingCofaceMapComplexPreadditiveYonedaDApp
section
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

namespace GlobalTheory

theorem alternatingCofaceMapComplex_preadditiveYoneda_d_apply {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) (m : ℕ)
  (x : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).X m) :
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1) x
   = (show X _⦋m+1⦌ ⟶ I from AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) := by
  have hd : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1)
      = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I) m := by
    exact CochainComplex.of_d (fun n => (X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋n⦌)
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I)) m
  rw [hd]
  let φ : (((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m⦌) ⟶ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)) →+ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌) :=
    AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)
  change φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _
  have h2 : (AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) =
      ∑ i : Fin (m+2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i ≫ (show X _⦋m⦌ ⟶ I from x)) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ => Preadditive.zsmul_comp _ _ _
  refine Eq.trans ?_ h2.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul]
  rfl

theorem alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ : ∀ {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) [Injective I] (n : ℕ), ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).ExactAt (n + 1) → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).ExactAt (n + 1) := by
  intro C _ _ X I _ n h
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x hx
  let S := ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).sc' (n+2) (n+1) n
  have hS1 : S.f = AlgebraicTopology.AlternatingFaceMapComplex.objD X (n+1) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X (n+1)
  have hS2 : S.g = AlgebraicTopology.AlternatingFaceMapComplex.objD X n :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X n
  let f : S.X₂ ⟶ I := x
  have hf : S.f ≫ f = 0 := by
    have h1 := alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I (n+1) x
    rw [hS1]
    exact h1.symm.trans hx
  have hm : Mono (cokernel.desc S.f S.g S.zero) := h.mono_cokernelDesc
  let g : S.X₃ ⟶ I := @Injective.factorThru _ _ _ _ _ _ (cokernel.desc S.f f hf) (cokernel.desc S.f S.g S.zero) hm
  refine ⟨g, ?_⟩
  change ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d n (n+1) g = x
  refine (alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I n g).trans ?_
  rw [← hS2]
  change S.g ≫ g = f
  have e2 : cokernel.desc S.f S.g S.zero ≫ g = cokernel.desc S.f f hf :=
    @Injective.comp_factorThru _ _ _ _ _ _ _ _ hm
  rw [← cokernel.π_desc S.f S.g S.zero, Category.assoc, e2, cokernel.π_desc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Injective EF → ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  first | (exact @GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (exact GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (intros; apply GlobalTheory.bilinForm_injective_exists_mul_mem_range  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelArtinianNoetherianSummand
section
namespace GlobalTheory

theorem ks_cancel_submodule (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P]
    [IsNoetherian R P] (N : Submodule R P) :
    ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'],
      Nonempty ((M × N) ≃ₗ[R] (M' × N)) → Nonempty (M ≃ₗ[R] M') := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro M M' _ _ _ _ e
  by_cases hind : ∀ A B : Submodule R N, IsCompl A B → A = ⊥ ∨ B = ⊥
  · exact _root_.GlobalTheory.cancel_summand_nilpotent_or_bijective R M M' N (_root_.GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective R N hind) e
  · push_neg at hind
    obtain ⟨A, B, hAB, hA, hB⟩ := hind
    have hAlt : A.map N.subtype < N := by
      have h1 : A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hB (by
        have := hAB.inf_eq_bot; rw [h, top_inf_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    have hBlt : B.map N.subtype < N := by
      have h1 : B < ⊤ := lt_top_iff_ne_top.mpr (fun h => hA (by
        have := hAB.inf_eq_bot; rw [h, inf_top_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    let eA : A ≃ₗ[R] A.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype A
    let eB : B ≃ₗ[R] B.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype B
    let eN : N ≃ₗ[R] (A.map N.subtype × B.map N.subtype) :=
      (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ LinearEquiv.prodCongr eA eB
    obtain ⟨e⟩ := e
    let f : ((M × A.map N.subtype) × B.map N.subtype) ≃ₗ[R]
        ((M' × A.map N.subtype) × B.map N.subtype) :=
      (LinearEquiv.prodAssoc R M _ _) ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R M) eN).symm ≪≫ₗ e ≪≫ₗ
        (LinearEquiv.prodCongr (LinearEquiv.refl R M') eN) ≪≫ₗ (LinearEquiv.prodAssoc R M' _ _).symm
    obtain ⟨g⟩ := ih _ hBlt _ _ ⟨f⟩
    exact ih _ hAlt M M' ⟨g⟩

theorem ks_cancel : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ _ _ ⟨e⟩
  let t : (⊤ : Submodule R P) ≃ₗ[R] P := Submodule.topEquiv
  exact ks_cancel_submodule R P ⊤ M M'
    ⟨(LinearEquiv.prodCongr (LinearEquiv.refl R M) t) ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.refl R M') t).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfNormOneValuationSubOneSmallStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small : ∀ (E : Type) [Field E] [NumberField E] (ε : E) (w : HeightOneSpectrum (𝓞 E)) (K : ℕ), Module.finrank ℚ E < K → (∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1) → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ)) → ε = 1 := by
  first | exact @GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | exact GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le | (intros; apply GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddMonoidHomOfLinearRelations
section
namespace GlobalTheory

theorem exists_addMonoidHom_of_linear_relations : ∀ (M ι T : Type) [AddCommGroup T] [Module ℚ T] (Y : ι → M → ℚ) (t : ι → T), (∀ (s : Finset ι) (c : ι → ℚ), ∑ i ∈ s, c i • Y i = 0 → ∑ i ∈ s, c i • t i = 0) → ∃ Ξ : (M → ℚ) →+ T, ∀ i, Ξ (Y i) = t i := by
  first
  | exact @_root_.GlobalTheory.NormBoundTheorem.main
  | exact _root_.GlobalTheory.NormBoundTheorem.main
  | (apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundTheorem.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAlStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent : ∀ {B A : Type} [inst : CommRing B] [IsDomain B] [inst_2 : CommRing A] [inst_3 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ}, Module.finrank B A = d → ∀ (y : Fin d → A), LinearIndependent B y → ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | exact GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_finset_sum_lt_of_forall_lt {K : Type*} [NormedField K] [IsUltrametricDist K]
    (s : Finset ℕ) (f : ℕ → K) {r : ℝ} (hr : 0 < r) (h : ∀ i ∈ s, ‖f i‖ < r) :
    ‖∑ i ∈ s, f i‖ < r := by
  first
  | exact @_root_.GlobalTheory.NormSumLt.main
  | exact _root_.GlobalTheory.NormSumLt.main
  | (apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormSumLt.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormSumLt.main ..)

theorem norm_le_one_of_isIntegral_int {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hz
  by_contra hlt
  push_neg at hlt
  set n := p.natDegree
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree,
    hm.leadingCoeff, map_one, one_mul] at hp
  set S := ∑ i ∈ Finset.range n, (algebraMap ℤ K) (p.coeff i) * z ^ i
  have hS : ‖S‖ < ‖z‖ ^ n := by
    refine norm_finset_sum_lt_of_forall_lt _ _ (pow_pos (by linarith) n) ?_
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ K) (p.coeff i)‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K _
    calc ‖(algebraMap ℤ K) (p.coeff i)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ = ‖z‖ ^ i := one_mul _
      _ < ‖z‖ ^ n := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  have h2 : z ^ n = -S := by linear_combination hp
  have h3 : ‖z‖ ^ n = ‖S‖ := by rw [← norm_pow, h2, norm_neg]
  linarith

theorem exists_embedding_padicAlgCl_place (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] : ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)),
      ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  let τ : E →+* PadicAlgCl l := (IsAlgClosed.lift : E →ₐ[ℚ] PadicAlgCl l).toRingHom
  have hle : ∀ x : 𝓞 E, ‖τ (x : E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral_int ((x.isIntegral_coe).map τ.toIntAlgHom)
  let I : Ideal (𝓞 E) :=
    { carrier := {x | ‖τ (x : E)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        push_cast
        rw [map_mul, norm_mul]
        calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
              mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hx }
  have hmem : ∀ x : 𝓞 E, x ∈ I ↔ ‖τ (x : E)‖ < 1 := fun x => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro x y hxy
      rw [hmem] at hxy
      rw [hmem, hmem]
      by_contra h
      push_neg at h
      have : 1 ≤ ‖τ ((x * y : 𝓞 E) : E)‖ := by
        push_cast
        rw [map_mul, norm_mul]
        exact one_le_mul_of_one_le_of_one_le h.1 h.2
      linarith
  have hne : I ≠ ⊥ := by
    intro hbot
    have hl : ((l : 𝓞 E)) ∈ I := by
      rw [hmem]
      have h1 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
      rw [h1, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l,
        PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [hbot, Ideal.mem_bot] at hl
    have h2 : ((l : 𝓞 E) : E) = 0 := by rw [hl]; rfl
    have h3 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
    rw [h3] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  exact ⟨τ, ⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZeroStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero : ∀ {k B A : Type} [inst : Field k] [Infinite k] [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra k B] [inst_5 : CommRing A] [inst_6 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ} (y : Fin d → A), (∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) → ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_field_combination_norm_ne_zero | exact GlobalTheory.exists_field_combination_norm_ne_zero | (intros; apply GlobalTheory.exists_field_combination_norm_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoin
section
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CenOrderIso

def toLocal (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* ℚ_[ℓ] ⊗[ℚ] F :=
  (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.toRingEquiv.toRingHom.comp
    ((Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom).toRingHom)

theorem toLocal_tmul (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (c : 𝓞 F) (a : ℤ_[ℓ]) :
    toLocal F ℓ (c ⊗ₜ[ℤ] a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := rfl

theorem toLocal_injective (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (toLocal F ℓ) := by
  have h1 : Function.Injective
      ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
  have h2 : Function.Injective
      ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 F) F)
  have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) := by
    have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) =
        ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) ∘
        ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) := by
      funext w
      induction w using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢; rw [ha, hb]
    rw [this]; exact h2.comp h1
  intro x y hxy
  apply hmap
  apply (Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).injective
  exact (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.injective hxy

theorem toLocal_mem (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (x : 𝓞 F ⊗[ℤ] ℤ_[ℓ]) :
    toLocal F ℓ x ∈ cenOrder ℓ F := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [toLocal_tmul]
    have hc : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) ∈ cenOrder ℓ F :=
      Algebra.subset_adjoin ⟨c, rfl⟩
    have : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) = a • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F)) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      show (a : ℚ_[ℓ]) = a • (1 : ℚ_[ℓ])
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Subalgebra.smul_mem _ hc a
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem cenOrder_le_range (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ y ∈ cenOrder ℓ F, ∃ x, toLocal F ℓ x = y := by
  let S : Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
    { (toLocal F ℓ).range with
      algebraMap_mem' := fun r => ⟨(1 : 𝓞 F) ⊗ₜ[ℤ] r, by
        rw [toLocal_tmul]; rfl⟩ }
  have hle : cenOrder ℓ F ≤ S := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact ⟨c ⊗ₜ[ℤ] (1 : ℤ_[ℓ]), by rw [toLocal_tmul]; simp⟩
  intro y hy
  exact hle hy

theorem cenOrder_equiv : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F,
      ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  intro F _ _ ℓ _
  let g : 𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* cenOrder ℓ F := (toLocal F ℓ).codRestrict (cenOrder ℓ F) (toLocal_mem F ℓ)
  have hbij : Function.Bijective g := by
    refine ⟨fun x y h => toLocal_injective F ℓ (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := cenOrder_le_range F ℓ y y.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g hbij, fun c => ?_⟩
  show toLocal F ℓ (c ⊗ₜ[ℤ] 1) = _
  rw [toLocal_tmul]; simp

end GlobalTheory.CenOrderIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFinite
section
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

namespace GlobalTheory.LocIso

theorem tensor_padicInt_equiv_locOrder : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  intro O _ _ _ ℓ _
  let g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom
  let g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp
      PadicInt.Coe.ringHom).toIntAlgHom
  have hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) := fun _ => rfl
  have hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O) := fun _ => rfl
  have hg : ∀ x y, Commute (g1 x) (g2 y) := by
    intro x y
    simp only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f := Algebra.TensorProduct.lift g1 g2 hg
  have hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
    intro o a
    simp only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hinj : Function.Injective f := by
    have hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘
          (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘
          (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul o a =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]
        rfl
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢
        rw [hx, hy]
    rw [heq]
    exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)
  have hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o a =>
      rw [hf]
      have h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) =
          algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [h1]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)
      exact ⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  let g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range :=
    (f.toRingHom).codRestrict _ hmem
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy
    rw [locOrder, Algebra.adjoin_eq_ring_closure] at hy'
    have hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪
        ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)
      · refine ⟨(1 : O) ⊗ₜ a, ?_⟩
        change f _ = _
        rw [hf, Algebra.TensorProduct.algebraMap_apply]
        rfl
      · refine ⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩
        change f _ = _
        rw [hf]
        simp
    obtain ⟨x, hx⟩ := hle hy'
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩
  change f (o ⊗ₜ 1) = _
  rw [hf]
  simp

end GlobalTheory.LocIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
section
set_option autoImplicit false

open CategoryTheory

universe v u

namespace GlobalTheory.CatH.DSq

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

theorem sign_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℤ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

end GlobalTheory.CatH.DSq
end

