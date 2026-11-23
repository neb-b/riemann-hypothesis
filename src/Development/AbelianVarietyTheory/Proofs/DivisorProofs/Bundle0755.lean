module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0728
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorAlgebraProductDiagramCompat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.KunnethOne

theorem tensor_eq_zero_of_forall {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V ⊗[K] W)
    (h : ∀ l : W →ₗ[K] K, TensorProduct.rid K V (LinearMap.lTensor V l t) = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K W
  have key : ∀ (j : Module.Free.ChooseBasisIndex K W) (s : V ⊗[K] W),
      TensorProduct.equivFinsuppOfBasisRight b s j =
        TensorProduct.rid K V (LinearMap.lTensor V (b.coord j) s) := by
    intro j s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  rw [key, h, map_zero, Finsupp.zero_apply]

section Contr

variable {K : Type} [Field K] {Q : Type} [Category.{0} Q] (G : Q ⥤ CommAlgCat.{0} K)
  [Fintype Q] [DecidableEq Q] [∀ T T' : Q, Fintype (T ⟶ T')] [∀ T T' : Q, DecidableEq (T ⟶ T')]

def coef (Λ : C1 G →ₗ[K] K) (T T' : Q) (φ : T ⟶ T') : G.obj T' →ₗ[K] K :=
  Λ ∘ₗ LinearMap.single K (fun T => ∀ (T' : Q) (_ : T ⟶ T'), G.obj T') T ∘ₗ
    LinearMap.single K (fun T' => (T ⟶ T') → G.obj T') T' ∘ₗ
    LinearMap.single K (fun _ : T ⟶ T' => G.obj T') φ

def contr (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) :
    (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') →ₗ[K] M :=
  ∑ T, ∑ T', ∑ φ : T ⟶ T', (TensorProduct.rid K M).toLinearMap ∘ₗ
    LinearMap.lTensor M (coef G Λ T T' φ) ∘ₗ
    LinearMap.proj (R := K) (φ := fun _ : T ⟶ T' => M ⊗[K] G.obj T') φ ∘ₗ
    LinearMap.proj (R := K) (φ := fun T' => (T ⟶ T') → M ⊗[K] G.obj T') T' ∘ₗ
    LinearMap.proj (R := K) (φ := fun T => ∀ (T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') T

theorem contr_apply (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G M Λ c = ∑ T, ∑ T', ∑ φ : T ⟶ T',
      TensorProduct.rid K M (LinearMap.lTensor M (coef G Λ T T' φ) (c T T' φ)) := by
  simp [contr, LinearMap.sum_apply]

theorem contr_tmul (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) (z : M)
    (h : C1 G) : contr G M Λ (fun T T' φ => z ⊗ₜ[K] h T T' φ) = Λ h • z := by
  rw [contr_apply]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, ← Finset.sum_smul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coef, LinearMap.comp_apply, ← map_sum]
  congr 1
  simp only [LinearMap.single_apply, Finset.univ_sum_single]

theorem contr_natural (M N : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Λ : C1 G →ₗ[K] K) (h : M →ₗ[K] N) (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G N Λ (fun T T' φ => LinearMap.rTensor (G.obj T') h (c T T' φ)) = h (contr G M Λ c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [contr_apply, map_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ =>
    Finset.sum_congr rfl fun φ _ => ?_
  induction c T T' φ using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem kunneth_contraction_d0_vanishes (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (hΛ : ∀ g : C0 G, Λ (d0 G g) = 0) (w : ∀ T : Q, M ⊗[K] G.obj T) :
    contr G M Λ (fun T T' φ => LinearMap.lTensor M (mp G φ).toLinearMap (w T) - w T') = 0 := by
  let D : (∀ T : Q, M ⊗[K] G.obj T) →ₗ[K] (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :=
    LinearMap.pi fun T => LinearMap.pi fun T' => LinearMap.pi fun φ =>
      LinearMap.lTensor M (mp G φ).toLinearMap ∘ₗ
        LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T -
      LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T'
  have hD : contr G M Λ ∘ₗ D = 0 := by
    refine LinearMap.pi_ext fun T₀ x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      have e : D (Pi.single T₀ (z ⊗ₜ[K] u)) =
          fun T T' φ => z ⊗ₜ[K] (-d0 G (Pi.single T₀ u : C0 G) T T' φ) := by
        funext T T' φ
        simp only [D, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, amitsur_d0_apply, neg_sub, TensorProduct.tmul_sub]
        by_cases h1 : T = T₀ <;> by_cases h2 : T' = T₀
        · subst h1; subst h2; simp
        · subst h1; simp [Pi.single_eq_of_ne h2]
        · subst h2; simp [Pi.single_eq_of_ne h1]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have c := contr_tmul G M Λ z (-d0 G (Pi.single T₀ u : C0 G))
      simp only [Pi.neg_apply] at c
      rw [LinearMap.comp_apply, e, c, map_neg, hΛ, neg_zero, zero_smul, LinearMap.zero_apply]
    | add u v hu hv => simp only [Pi.single_add, map_add (f := _), hu, hv]
  exact LinearMap.congr_fun hD w

end Contr

end GlobalTheory.CatCoh.KunnethOne

namespace GlobalTheory.CatCoh.KunnethOne

theorem sum_tmul_eq_zero_of_cup : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  intro K _ P Q _ _ _ _ F G E i₁ i₂ h₁ h₂ hb n x y f hf
  classical
  haveI := Fintype.ofFinite Q
  haveI : ∀ T T' : Q, Fintype (T ⟶ T') := fun _ _ => Fintype.ofFinite _
  apply tensor_eq_zero_of_forall
  intro l
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l ∘ₗ H1.mk G)
  have hΛy : ∀ z : Z1 G, Λ z.1 = l (H1.mk G z) := fun z => LinearMap.congr_fun hΛ z
  have hΛd : ∀ g : C0 G, Λ (d0 G g) = 0 := fun g => by
    have e := hΛy ⟨d0 G g, commAlgFunctorCoboundaryZero_mem_cocyclesOne G g⟩
    rw [e, H1.mk_eq_zero.2 ⟨g, rfl⟩, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← hΛy, ← map_smul, ← map_sum]
  rw [H1.mk_eq_zero]
  let β : ∀ T : P × Q, F.obj T.1 ⊗[K] G.obj T.2 ≃ₐ[K] E.obj T :=
    fun T => AlgEquiv.ofBijective _ (hb T)
  have hβ : ∀ (T : P × Q) (z : F.obj T.1) (u : G.obj T.2), β T (z ⊗ₜ u) = i₁ T z * i₂ T u :=
    fun T z u => Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have natL : ∀ (p p' : P) (T : Q) (a : p ⟶ p') (t : F.obj p ⊗[K] G.obj T),
      β (p', T) (LinearMap.rTensor (G.obj T) (mp F a).toLinearMap t) =
        mp E ((a, 𝟙 T) : (p, T) ⟶ (p', T)) (β (p, T) t) := by
    intro p p' T a t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.rTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p', T), ← h₂ (p, T) (p', T)]
      simp [mp_id]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have natR : ∀ (p : P) (T T' : Q) (b : T ⟶ T') (t : F.obj p ⊗[K] G.obj T),
      β (p, T') (LinearMap.lTensor (F.obj p) (mp G b).toLinearMap t) =
        mp E ((𝟙 p, b) : (p, T) ⟶ (p, T')) (β (p, T) t) := by
    intro p T T' b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.lTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p, T'), ← h₂ (p, T) (p, T')]
      simp [mp_id]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  refine ⟨fun p => contr G (F.obj p) Λ
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T')))), ?_⟩
  funext p p' a
  rw [amitsur_d0_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have step : ∀ (T T' : Q) (b : T ⟶ T'),
      (β (p', T')).symm (f (p', T) (p', T') ((𝟙 p', b) : (p', T) ⟶ (p', T'))) -
        LinearMap.rTensor (G.obj T') (mp F a).toLinearMap
          ((β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, b) : (p, T) ⟶ (p, T')))) =
      ∑ i, (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' b -
        (LinearMap.lTensor (F.obj p') (mp G b).toLinearMap
            ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
          (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T')))) := by
    intro T T' b
    apply (β (p', T')).injective
    have H1 := hf (p, T) (p', T) (p', T') (a, 𝟙 T) (𝟙 p', b)
    have H2 := hf (p, T) (p, T') (p', T') (𝟙 p, b) (a, 𝟙 T')
    rw [d1_apply] at H1 H2
    simp only [prod_comp, Category.comp_id, Category.id_comp] at H1 H2
    simp only [Z1.id, map_zero, zero_mul, Finset.sum_const_zero] at H2
    simp only [← h₁, mp_id] at H1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, AlgEquiv.apply_symm_apply, natL, natR, hβ]
    linear_combination H1 - H2
  have nat := contr_natural G (F.obj p) (F.obj p') Λ (mp F a).toLinearMap
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T'))))
  rw [AlgHom.toLinearMap_apply] at nat
  rw [← nat, ← map_sub]
  trans contr G (F.obj p') Λ ((∑ i, fun T T' φ => (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' φ) -
    fun T T' φ => LinearMap.lTensor (F.obj p') (mp G φ).toLinearMap
        ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
      (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T'))))
  · congr 1
    funext T T' b
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact step T T' b
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, kunneth_contraction_d0_vanishes _ _ _ hΛd, sub_zero, map_sum]
    simp only [contr_tmul]

end GlobalTheory.CatCoh.KunnethOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCMIsFieldOrNormSurjective
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormDichotomy

theorem unit_or_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], (∀ a : K ⊗[F] E, a ≠ 0 → IsUnit a) ∨ (∀ k : K, k ≠ 0 → ∃ t : K ⊗[F] E, t * sigR K σ t = algebraMap K (K ⊗[F] E) k) := by
  intro F E _ _ _ _ _ σ h K _ _

  obtain ⟨e, he⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set d : E := e - σ e with hd
  have hσd : σ d = -d := by
    rw [hd, map_sub, GlobalTheory.HermLineZeros.conj_invol h]; ring
  have hd0 : d ≠ 0 := by
    intro h0; apply he; rw [hd, sub_eq_zero] at h0; exact h0.symm
  have hfix : σ (d * d) = d * d := by rw [map_mul, hσd]; ring
  obtain ⟨c0, hc0⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h _ hfix
  haveI : CharZero F := inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  set L := K ⊗[F] E
  set ι := algebraMap K L with hι
  set D : L := inclR K d with hD
  set c : K := algebraMap F K c0 with hc
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; apply hd0; rw [map_zero] at hc0; exact mul_self_eq_zero.1 hc0.symm
  have hcne : c ≠ 0 := by rw [hc]; exact (map_ne_zero _).2 hc0ne
  have hDD : D * D = ι c := by
    rw [hD, ← map_mul, ← hc0, hc, hι, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] K ⊗[F] E).commutes c0
  have hsD : sigR K σ D = -D := by
    show inclR K (σ d) = _
    rw [hσd, map_neg]
  have hst : ∀ t : K, sigR K σ (ι t) = ι t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl

  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst0
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst0
    have e2 := congrArg σ hst0
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσd, map_zero] at e2
    have ht : algebraMap F E t * d = 0 := by linear_combination (hst0 - e2) / 2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h1 | h1
      · exact (map_eq_zero _).1 h1
      · exact absurd h1 hd0
    refine ⟨?_, ht0⟩
    rw [ht0, map_zero, zero_mul, add_zero] at hst0
    exact (map_eq_zero _).1 hst0
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [h.2.2.1]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bK := Algebra.TensorProduct.basis K b
  have hdec : ∀ a : L, ∃ u v : K, a = ι u + ι v * D := by
    intro a
    refine ⟨bK.repr a 0, bK.repr a 1, ?_⟩
    conv_lhs => rw [← bK.sum_repr a]
    rw [Fin.sum_univ_two]
    have hb : ⇑b = ![(1 : E), d] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have h0 : bK 0 = 1 := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_zero]; rfl
    have h1 : bK 1 = D := by
      simp only [bK, Algebra.TensorProduct.basis_apply, hb, Matrix.cons_val_one, Matrix.head_cons]; rfl
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
  by_cases hsq : ∃ r : K, r * r = c
  · right
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; exact hcne (by rw [← hr, mul_zero])
    have h2 : ι (1 / 2) * 2 = 1 := by
      rw [show (2 : L) = ι 2 from (map_ofNat ι 2).symm, ← map_mul]; norm_num
    have hs : ι r * ι r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hr0, map_one]
    have hD2 : D * D = ι r * ι r := by rw [hDD, ← hr, map_mul]
    set ε : L := ι (1 / 2) * (1 + ι r⁻¹ * D) with hε
    have he0 : ε * (1 - ε) = 0 := by
      rw [hε]
      linear_combination (-(1 + ι r⁻¹ * D) * ι (1 / 2)) * h2 + (-ι (1 / 2) ^ 2 * ι r⁻¹ ^ 2) * hD2 + (-ι (1 / 2) ^ 2 * (ι r⁻¹ * ι r + 1)) * hs
    have hσε : sigR K σ ε = 1 - ε := by
      rw [hε, map_mul, map_add (f := _), map_mul, map_one, hst, hst, hsD]
      linear_combination h2
    intro k _
    refine ⟨ι k * ε + (1 - ε), ?_⟩
    rw [map_add (f := _), map_mul, map_sub, map_one, hst, hσε]
    linear_combination (ι k ^ 2 + 1 - 2 * ι k) * he0
  · left
    push_neg at hsq
    intro a ha
    obtain ⟨u, v, rfl⟩ := hdec a
    have hn : u * u - c * (v * v) ≠ 0 := by
      intro h0
      by_cases hv : v = 0
      · apply ha
        have : u * u = 0 := by rw [hv] at h0; simpa using h0
        rw [mul_self_eq_zero.1 this, hv, map_zero, zero_mul, add_zero]
      · apply hsq (u / v)
        field_simp
        linear_combination h0
    have hN : (ι u + ι v * D) * sigR K σ (ι u + ι v * D) = ι (u * u - c * (v * v)) := by
      rw [map_add (f := _), map_mul, hst, hst, hsD, map_sub, map_mul, map_mul, map_mul]
      linear_combination (-(ι v * ι v)) * hDD
    refine IsUnit.of_mul_eq_one (sigR K σ (ι u + ι v * D) * ι (u * u - c * (v * v))⁻¹) ?_
    rw [← mul_assoc, hN, ← map_mul, mul_inv_cancel₀ hn, map_one]

end GlobalTheory.NormDichotomy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordsMemOfOdd
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem torsion_coords_mem_of_odd : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ (hu : u ≠ 0) (r s t : ℂ), IntV V ((⟨Units.mk0 u hu, r, s, t⟩ : VariableChange ℂ) • latticeCurve L) → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (L.weierstrassP z - r) / u ^ 2 ∈ V ∧ (L.derivWeierstrassP z / 2 - t - s * (L.weierstrassP z - r)) / u ^ 3 ∈ V := by
  intro L β u V N hmul hβ hΔ hN hodd hu r s t hint z hz hNz
  have h2z : 2 * z ∉ L.lattice := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    have e : z = (N : ℂ) * z - ((k : ℤ) • (2 * z)) := by
      rw [zsmul_eq_mul, hk]; push_cast; ring
    exact hz (e ▸ sub_mem hNz (L.lattice.smul_mem _ h))
  have hNz2 : (N : ℂ) * (2 * z) ∈ L.lattice := by
    have e : (N : ℂ) * (2 * z) = N * z + N * z := by ring
    rw [e]; exact add_mem hNz hNz
  obtain ⟨hP', -⟩ := _root_.GlobalTheory.CMModel.TorsMemVal.main L β u V N hmul hβ hΔ hN z z hz hz hNz hNz
  obtain ⟨-, hδ⟩ := _root_.GlobalTheory.CMModel.TorsMemVal.main L β u V N hmul hβ hΔ hN (2 * z) z h2z hz hNz2 hNz
  have dup := GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq L z hz h2z
  have sq := L.derivWeierstrassP_sq z hz
  set C : VariableChange ℂ := ⟨Units.mk0 u hu, r, s, t⟩ with hC
  have hCu : ((C.u⁻¹ : ℂˣ) : ℂ) = u⁻¹ := by simp [hC]
  have hCr : C.r = r := rfl
  have hCs : C.s = s := rfl
  have hCt : C.t = t := rfl
  set P := L.weierstrassP z with hPdef
  set P' := L.derivWeierstrassP z with hP'def
  set P2 := L.weierstrassP (2 * z) with hP2def
  have hD : 2 * ((P' / 2 - t - s * (P - r)) / u ^ 3) + (C • latticeCurve L).a₁ * ((P - r) / u ^ 2)
      + (C • latticeCurve L).a₃ = P' / u ^ 3 := by
    rw [variableChange_a₁, variableChange_a₃, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    field_simp
    ring
  apply _root_.GlobalTheory.CMModel.mem_of_duplication_eq V (C • latticeCurve L) _ _ ((P2 - P) / u ^ 2) hint
  · rw [Affine.equation_iff]
    simp only [WeierstrassCurve.toAffine]
    rw [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, hCu, hCr, hCs, hCt]
    simp only [latticeCurve]
    linear_combination (norm := skip) (1 / 4 * u⁻¹ ^ 6) * sq
    field_simp
    ring
  · rw [hD]; exact hP'
  · exact hδ
  · rw [hD, variableChange_b₄, variableChange_b₆, variableChange_b₈, hCu, hCr]
    simp only [latticeCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (norm := skip) (u⁻¹ ^ 8) * (-dup + (2 * P + r) * sq)
    field_simp
    ring

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeValNN

theorem typePrime_valuationSum_eq_logGap_all (D : D7) (X : ErrX D) : Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond D X := by
  intro i u j _ S hS
  have h1 : ∀ w ∈ S, SizeData₂.sz w (vNN X i u j w) =
      ∑ τ : D.what₂.Tau, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) := by
    intro w _
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    unfold SizeData₂.sz vNN
    rw [mul_div_cancel₀ _ he, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, GlobalTheory.TypeLoss.sum_half D _ (D.host.g_prime i) S hS _ (GlobalTheory.TypeLoss.tauPib_norm X i τ)]

theorem typePrime_valuationSum_eq_logGap_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX :=
  fun Fm x hx i => typePrime_valuationSum_eq_logGap_all (Fm.D x i) (Fm.ex x hx i).errX

end GlobalTheory.TypeValNN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem units_of_divConst (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    (h : DivConst T O)
    (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) :
    ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧
      (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O d) =
        algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O c) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  by_cases hL : Subsingleton (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
  · exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, Subsingleton.elim _ _⟩
  rw [not_subsingleton_iff_nontrivial] at hL
  obtain ⟨⟨b, s₁⟩, hb⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨⟨c, s₂⟩, hc⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨t₁, ht₁, hs₁⟩ := s₁.2
  obtain ⟨t₂, ht₂, hs₂⟩ := s₂.2
  have h1 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ((s₁ : O) * (s₂ : O)) := by
    have hu : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) = 1 := u.mul_inv
    rw [← hb, ← hc, ← IsLocalization.mk'_mul] at hu
    have := IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) (s₁ * s₂)
    rw [hu, one_mul] at this
    rw [← this]; rfl
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).1 h1
  obtain ⟨t₀, ht₀, hm₀⟩ := m.2
  have hmem : t₀ * t₁ * t₂ ∈ nonZeroDivisors T :=
    mul_mem (mul_mem ht₀ ht₁) ht₂
  have hne : t₀ * t₁ * t₂ ≠ 0 := nonZeroDivisors.ne_zero hmem
  obtain ⟨a, w, hbw⟩ := h b ((m : O) * c) (t₀ * t₁ * t₂) hne (by
    rw [map_mul, map_mul, hm₀, hs₁, hs₂]
    calc b * ((m : O) * c) = (m : O) * (b * c) := by ring
      _ = (m : O) * ((s₁ : O) * (s₂ : O)) := hm
      _ = (m : O) * (s₁ : O) * (s₂ : O) := by ring)
  have key : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b := by
    rw [← hb]; exact IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b s₁
  refine ⟨a, t₁, w, ?_, nonZeroDivisors.ne_zero ht₁, ?_⟩
  · intro ha
    have h0 : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = 0 := by
      rw [key, hbw, ha]; simp
    exact (u.isUnit.mul (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s₁)).ne_zero h0
  · rw [hs₁, key, hbw, map_mul]

theorem main_of_divConstAll (hAll : DivConstAll) : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  intro T O _ _ _ _ _ _ _ _ _ hroot hO u
  obtain ⟨P, hP, φ, hφ, hsh⟩ :=
    GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hO
  exact units_of_divConst T O (hAll T O hroot P φ hφ hsh) u

end GlobalTheory.VertUnits

namespace GlobalTheory.VertUnits

theorem units_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) :=
  main_of_divConstAll (_root_.GlobalTheory.VertUnits.divConstAll_of_divConstLocal (divConstLocal_of
    (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin) (_root_.GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin))))

end GlobalTheory.VertUnits
end

