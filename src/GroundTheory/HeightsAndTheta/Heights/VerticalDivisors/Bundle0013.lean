module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartPointTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChartPointTrdeg.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : AffineChartTrdeg.Statement) :
    ChartPointTrdeg.Statement := by
  intro k L _ _ _ n e Q g hQ hg x j₀ hx hj
  have := hQ.isPrime
  have hdim := h₁ k n (e + 1) Q g hQ hg
  have hXj : (X j₀ : MvPolynomial (Fin n) k) ∉ Q := fun h => hj (by simpa using hx _ h)
  have htr := h₂ k n e Q j₀ hQ hdim hXj
  let R := MvPolynomial (Fin n) k ⧸ Q
  let K := FractionRing R
  let π : R →ₐ[k] L := Ideal.Quotient.liftₐ Q (aeval x) hx
  let s : R := Ideal.Quotient.mk Q (X j₀)
  have hs : s ≠ 0 := by
    intro h
    exact hXj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hπX : ∀ m, π (Ideal.Quotient.mk Q (X m)) = x m := fun m =>
    (AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp Q (aeval x) hx) (X m)).trans (aeval_X x m)
  have hπs : π s = x j₀ := hπX j₀
  have hπu : IsUnit (π s) := by rw [hπs]; exact hj.isUnit
  have hKs : algebraMap R K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs
  let S := Localization.Away s
  let ρ : S →ₐ[k] L := IsLocalization.Away.liftAlgHom s hπu
  let ι : S →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom k R K) s hKs.isUnit
  have hSinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hι : Function.Injective ι := by
    show Function.Injective (IsLocalization.Away.lift (g := algebraMap R K) s hKs.isUnit)
    refine (IsLocalization.lift_injective_iff _).mpr fun a b => ?_
    rw [hSinj.eq_iff, (IsFractionRing.injective R K).eq_iff]
  let y : Fin n → S := fun m => algebraMap R S (Ideal.Quotient.mk Q (X m)) * IsLocalization.Away.invSelf s
  have hinv : ∀ {B : Type} [Field B] [Algebra k B] (φ : S →ₐ[k] B),
      φ (IsLocalization.Away.invSelf s) = (φ (algebraMap R S s))⁻¹ := by
    intro B _ _ φ
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  have hιR : ∀ a, ι (algebraMap R S a) = algebraMap R K a := fun a =>
    IsLocalization.Away.lift_eq (g := algebraMap R K) s hKs.isUnit a
  have hρR : ∀ a, ρ (algebraMap R S a) = π a := fun a =>
    IsLocalization.Away.lift_eq (g := (π : R →+* L)) s hπu a
  have hιy : ι ∘ y = fun m => genPt Q m * (genPt Q j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ι, hιR]
    rfl
  have hρy : ρ ∘ y = fun m => x m * (x j₀)⁻¹ := by
    funext m
    simp only [Function.comp_apply, y, map_mul, hinv ρ, hρR, hπX, s]
  let T := Algebra.adjoin k (Set.range y)
  have hA : T.map ι = Algebra.adjoin k (Set.range fun m => genPt Q m * (genPt Q j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hιy]
  have hB : T.map ρ = Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹) := by
    rw [← Algebra.adjoin_image, ← Set.range_comp, hρy]
  have hTA : Algebra.trdeg k T = Algebra.trdeg k (T.map ι) :=
    (Subalgebra.equivMapOfInjective T ι hι).trdeg_eq
  have hBT : Algebra.trdeg k (T.map ρ) ≤ Algebra.trdeg k T := by
    refine trdeg_le_of_surjective ((ρ.comp T.val).codRestrict (T.map ρ)
      (fun t => ⟨t, t.2, rfl⟩)) ?_
    rintro ⟨b, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hB]
  rw [hA, htr] at hTA
  exact hBT.trans hTA.le

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PDerivSpanTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

theorem DerivSpanTrdeg.derivation_eq_zero_of_isSeparable {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by
  have hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact D.map_algebraMap x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
    | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  ext α
  set E := IntermediateField.adjoin k s
  have hsep : IsSeparable E α := Algebra.IsSeparable.isSeparable E α
  set g : Polynomial K := (minpoly E α).map (algebraMap E K)
  have h0 : D (g.eval α) = 0 := by
    rw [Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  have hc : D.mapCoeffs g = 0 := by
    ext i
    simp only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]
    exact (hE _ ((minpoly E α).coeff i).2).trans (by simp)
  rw [Derivation.apply_eval_eq, hc, map_zero, zero_add] at h0
  have hne : g.derivative.eval α ≠ 0 := by
    simp only [g]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval E α)
  simpa [hne] using h0

theorem DerivSpanTrdeg.proof : DerivSpanTrdeg.Statement := by
  intro k L _ _ _ _ ι _ z e he
  classical
  set F₀ := IntermediateField.adjoin k (Set.range z)
  have : Algebra.EssFiniteType k F₀ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨Finset.univ.image z, by simp [F₀]⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F₀
  have htr : Algebra.trdeg k F₀ = Algebra.trdeg k (Algebra.adjoin k (Set.range z)) := by
    have := trdeg_add_eq k (Algebra.adjoin k (Set.range z)) (A := F₀)
    rw [trdeg_eq_zero (R := Algebra.adjoin k (Set.range z)) (A := F₀), add_zero] at this
    exact this.symm
  have hcard : s.card ≤ e := by
    have h1 := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h1
    exact_mod_cast h1 ▸ he
  let N : Submodule F₀ Ω[F₀⁄k] :=
    Submodule.span F₀ (Set.range fun x : s => KaehlerDifferential.D k F₀ x)
  have hspan : N = ⊤ := by
    have hD := DerivSpanTrdeg.derivation_eq_zero_of_isSeparable (M := Ω[F₀⁄k] ⧸ N) (s : Set F₀)
      (N.mkQ.compDer (KaehlerDifferential.D k F₀)) (fun x hx => by
        change N.mkQ (KaehlerDifferential.D k F₀ x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun D => D x) hD
    simpa [Submodule.Quotient.mk_eq_zero] using this
  have hr : Module.finrank F₀ Ω[F₀⁄k] ≤ e := by
    have h := finrank_range_le_card (R := F₀) (fun x : s => KaehlerDifferential.D k F₀ x)
    change Module.finrank F₀ N ≤ _ at h
    rw [hspan, finrank_top, Fintype.card_coe] at h
    exact h.trans hcard
  let ω := Module.finBasis F₀ Ω[F₀⁄k]
  refine ⟨Module.finrank F₀ Ω[F₀⁄k], hr, fun m j =>
    ω.repr (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) m, ?_⟩
  intro D
  let D' : Derivation k F₀ L := D.compAlgebraMap F₀
  let φ := (KaehlerDifferential.linearMapEquivDerivation k F₀).symm D'
  refine ⟨fun m => φ (ω m), fun j => ?_⟩
  have h1 : D (z j) =
      φ (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) := by
    have h := LinearEquiv.apply_symm_apply (KaehlerDifferential.linearMapEquivDerivation k F₀) D'
    exact (congrArg (fun D'' : Derivation k F₀ L =>
      D'' ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) h).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← ω.sum_repr (KaehlerDifferential.D k F₀ _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenSecSeparable

theorem genPar_algIndep (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

theorem adjoin_secCoord {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

theorem secCoord_form {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) (i : Fin e) :
    ∑ j, algebraMap E (SecAlg Q y) (y (.inl (i, j))) * secCoord Q y j = 0 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (secForm y i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem secCoord_chart {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

theorem aeval_secCoord (k : Type*) [Field k] (e : ℕ) {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) (hf : f ∈ Q) :
    aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)) f = 0 := by
  set I := secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)
  have key : ((aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n)) : MvPolynomial (Fin n) k →ₐ[k] GenSec k e Q) : MvPolynomial (Fin n) k →+* _) =
      (Ideal.Quotient.mk I).comp (MvPolynomial.map (algebraMap k (GenParField k e n))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_coe, aeval_C, RingHom.coe_comp, Function.comp_apply, map_C]
      rw [IsScalarTower.algebraMap_apply k (GenParField k e n) (GenSec k e Q)]
      rfl
    · intro j
      simp only [RingHom.coe_coe, aeval_X, RingHom.coe_comp, Function.comp_apply, map_X]
      rfl
  have h := congrArg (fun φ => φ f) key
  simp only [RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply] at h
  rw [h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

end GenSecSeparable

open GenSecSeparable in
theorem GenSecSeparable.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : ChartPointTrdeg.Statement) (h₄ : SecPointSeparable.Statement) :
    GenSecSeparable.Statement := by
  intro k _ _ n e Q g hQ hg
  have : Module.Finite (GenParField k e n) (GenSec k e Q) :=
    h₁ k (GenParField k e n) n e Q g (genPar k e n) (genPar_algIndep k e n) hQ hg
  have : IsDomain (GenSec k e Q) := h₂ k n e Q g hQ hg
  let : Field (GenSec k e Q) :=
    (isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)).toField
  exact h₄ k n e (GenSec k e Q) _ (adjoin_secCoord _ _) (secCoord_form _ _) (secCoord_chart _ _)
    fun j₀ hj₀ => h₃ k (GenSec k e Q) n e Q g hQ hg _ j₀ (aeval_secCoord k e Q) hj₀

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFormsKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem GenericFormsKer.proof : GenericFormsKer.Statement := by
  intro F L _ _ _ ι _ e r hre u hu b c h j
  classical

  set V : Submodule F (ι → F) := Submodule.span F (Set.range b) with hV
  set B := Module.finBasis F V
  set r' := Module.finrank F V
  have hr' : r' ≤ e := (finrank_range_le_card b).trans (by simpa using hre)
  let v : Fin r' → ι → F := fun l => (B l : ι → F)
  have hbm : ∀ m, b m ∈ V := fun m => Submodule.subset_span ⟨m, rfl⟩

  let c' : Fin r' → L := fun l => ∑ m, c m * algebraMap F L (B.repr ⟨b m, hbm m⟩ l)
  have hw : ∀ j, ∑ m, c m * algebraMap F L (b m j) = ∑ l, c' l * algebraMap F L (v l j) := by
    intro j
    have hexp : ∀ m, b m j = ∑ l, B.repr ⟨b m, hbm m⟩ l * v l j := by
      intro m
      have := congrFun (congrArg Subtype.val (B.sum_repr ⟨b m, hbm m⟩)) j
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hexp, map_sum, map_mul, Finset.mul_sum, c', Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

  let M : Matrix (Fin r') (Fin r') L :=
    fun i l => ∑ j, u (Fin.castLE hr' i, j) * algebraMap F L (v l j)
  have hMc : M.mulVec c' = 0 := by
    funext i
    have hi := h (Fin.castLE hr' i)
    simp only [hw] at hi
    simp only [Matrix.mulVec, dotProduct, M, Pi.zero_apply, Finset.sum_mul]
    rw [Finset.sum_comm, ← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  let P : Matrix (Fin r') (Fin r') (MvPolynomial (Fin e × ι) F) :=
    fun i l => ∑ j, X (Fin.castLE hr' i, j) * C (v l j)
  have hPM : (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L).toRingHom.mapMatrix P = M := by
    ext i l
    change aeval u (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = M i l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, aeval_X, aeval_C, M]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  let A₀ : Fin r' → ι → F := fun l j => B.repr (g (Pi.single j 1)) l
  have hA₀ : ∀ i l, ∑ j, A₀ i j * v l j = if i = l then 1 else 0 := by
    intro i l
    have hvl : (∑ j, v l j • (Pi.single j (1 : F) : ι → F)) = V.subtype (B l) := by
      funext k
      simp [v, Finset.sum_apply, Pi.single_apply]
    have := congrArg (fun x => B.repr (g x) i) hvl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at this
    rw [← LinearMap.comp_apply, hg, LinearMap.id_apply, Module.Basis.repr_self_apply] at this
    have hil : (if i = l then (1 : F) else 0) = if l = i then 1 else 0 := by
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [hil, ← this]
    simp only [A₀]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  let x : Fin e × ι → F := fun p => if hp : p.1.val < r' then A₀ ⟨p.1.val, hp⟩ p.2 else 0
  have hPx : (eval x).mapMatrix P = 1 := by
    ext i l
    change eval x (∑ j, X (Fin.castLE hr' i, j) * C (v l j)) = (1 : Matrix (Fin r') (Fin r') F) i l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_X, eval_C, Matrix.one_apply]
    rw [← hA₀]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [x, Fin.castLE]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg (eval x) h0
    rw [RingHom.map_det, hPx, Matrix.det_one, map_zero] at this
    exact one_ne_zero this
  have hMdet : M.det ≠ 0 := by
    rw [← hPM, ← RingHom.map_det]
    have hinj : Function.Injective (aeval u : MvPolynomial (Fin e × ι) F →ₐ[F] L) :=
      algebraicIndependent_iff_injective_aeval.1 hu
    exact (map_ne_zero_iff _ hinj).2 hPdet
  have hc' : c' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hMdet hMc
  rw [hw]
  simp [hc']

end

end GroundTheory.Heights₂.Heights.Vertical
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecFirstNeField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem exists_relComps_of_mem_incidence_field {F : Type*} [Field F] {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) F)} {v : Fin k × Fin n → AlgebraicClosure F}
    (hv : v ∈ incidence J k) : ∃ W ∈ relComps J, v ∈ incidence W k := by
  obtain ⟨x, hx0, hxJ, hxv⟩ := hv
  have hP : (RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F)).IsPrime :=
    RingHom.ker_isPrime _
  have hJP : J ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) :=
    fun g hg => RingHom.mem_ker.mpr (hxJ g hg)
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hJP
  refine ⟨W, ⟨hW, ?_⟩, x, hx0, fun g hg => RingHom.mem_ker.mp (hWP hg), hxv⟩
  by_contra hrel
  apply hx0
  funext j
  have hj : X j ∈ W := by
    by_contra hj
    exact hrel ⟨j, hj⟩
  simpa using RingHom.mem_ker.mp (hWP hj)

theorem SpecFirstNeField.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₃ : ChowFormExists.Statement) (h₄ : IncidenceZeroLocus.Statement) :
    SpecFirstNeField.Statement := by
  classical
  intro F _ n e I f u hI hf hu h0
  have hdim := h₁ F n (e + 1) I f hI hf

  have hG : ∀ W : Ideal (MvPolynomial (Fin n) F), ∃ g : MvPolynomial (Fin e × Fin n) F,
      g ≠ 0 ∧ (W ∈ relComps (I ⊔ Ideal.span {linForm u}) → IsChowForm W e g) := by
    intro W
    by_cases hW : W ∈ relComps (I ⊔ Ideal.span {linForm u})
    · obtain ⟨hWp, hWd⟩ := h₂ F n e I W u hI hdim hu hW
      obtain ⟨g, hg⟩ := h₃ F n e W hWp hWd
      exact ⟨g, hg.1, fun _ => hg⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hW⟩
  choose G hG0 hGc using hG
  let S := ((I ⊔ Ideal.span {linForm u}).finite_minimalPrimes_of_isNoetherianRing _).toFinset
  have hprod : ∀ v : Fin e × Fin n → AlgebraicClosure F, aeval v (∏ W ∈ S, G W) = 0 := by
    intro v
    let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
      Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (u ij.2))
        (fun i => v (i, ij.2)) ij.1
    have hw : aeval w f = 0 := by
      have hs : aeval v (specFirst f u) = aeval w f := by
        have hfun : (fun ij => aeval v (specFirstVar u ij)) = w := by
          funext ij
          obtain ⟨i, j⟩ := ij
          induction i using Fin.cases with
          | zero => simp [specFirstVar, w]
          | succ i => simp [specFirstVar, w]
        unfold specFirst
        rw [aeval_bind₁, hfun]
      rw [← hs, h0, map_zero]
    have hinc : ∀ g ∈ GroundTheory.Heights₂.Heights.incIdeal I (e + 1), aeval w g = 0 := by
      intro g hg
      simp only [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 hg
      rw [map_mul, hw, zero_mul]
    obtain ⟨y, hy0, hyI, hyw⟩ := h₄ F n (e + 1) I hI.isHomog (AlgebraicClosure F) w hinc
    have hvJ : v ∈ incidence (I ⊔ Ideal.span {linForm u}) e := by
      refine ⟨y, hy0, fun g hg => ?_, fun i => by simpa [w] using hyw i.succ⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      have hu0 : aeval y (linForm u) = 0 := by
        simpa [w, linForm] using hyw 0
      rw [map_add (f := _), map_mul, hu0, mul_zero, add_zero, hyI a ha]
    obtain ⟨W, hW, hvW⟩ := exists_relComps_of_mem_incidence_field hvJ
    rw [map_prod]
    exact Finset.prod_eq_zero ((Set.Finite.mem_toFinset _).mpr hW.1)
      (((hGc W hW).2 (G W)).2 dvd_rfl v hvW)
  have hne : (∏ W ∈ S, G W) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hG0 W
  apply hne
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F _).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro v
  rw [eval_map, ← aeval_def, hprod v, map_zero]

end

end GroundTheory.Heights₂.Heights.Vertical
end

