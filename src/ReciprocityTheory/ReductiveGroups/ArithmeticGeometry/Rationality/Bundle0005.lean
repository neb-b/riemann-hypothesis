module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.UnitPointLiftBall
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCorePf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finCore_holds : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖AddMonoidAlgebra.coeff p μ‖ ∧
        AddMonoidAlgebra.coeff p μ ≠ 0 ∧ ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖AddMonoidAlgebra.coeff p ν‖) hne
    have hc : AddMonoidAlgebra.coeff p μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : AddMonoidAlgebra.coeff p ν = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖AddMonoidAlgebra.coeff p μ‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p ν‖
          ≤ ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p μ‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = AddMonoidAlgebra.coeff p μ *
        MvPolynomial.eval x (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push Not at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCorePf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

theorem exists_finset_inf_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by
  classical
  let T : Set (Submodule K V) :=
    {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}
  have hT : T.Nonempty := ⟨⊤, ∅, by simp, by simp⟩
  obtain ⟨N0, hN0, hmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min T hT
  obtain ⟨t0, ht0S, rfl⟩ := hN0
  refine ⟨t0, ht0S, fun N hN => ?_⟩
  have hmem : (insert N t0).inf id ∈ T :=
    ⟨insert N t0, by
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨hN, ht0S⟩, rfl⟩
  have hle : (insert N t0).inf id ≤ t0.inf id := Finset.inf_mono (Finset.subset_insert _ _)
  have heq : (insert N t0).inf id = t0.inf id := eq_of_le_of_not_lt hle (hmin _ hmem)
  rw [Finset.inf_insert] at heq
  calc t0.inf id = N ⊓ t0.inf id := heq.symm
    _ ≤ N := inf_le_left

theorem kerCore_holds : KerCoreStatement := by
  intro K _ _ V _ _ _ W Fam hkill hdet henl
  classical

  let S : Set (Submodule K V) := {N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
    (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}
  obtain ⟨t, htS, htinf⟩ := exists_finset_inf_eq S
  have hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
      (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f := fun N => htS N.2
  choose Ki fKi nfKi aKi fi hfam hNker using hmem
  have hWinf : t.inf id = W := by
    apply le_antisymm
    · intro v hv
      apply hdet v
      intro K₁ _ _ _ f hf
      have := htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv
      exact this
    · refine Finset.le_inf fun N hN => ?_
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      show W ≤ N
      rw [h1]
      exact hkill _ _ (hfam ⟨N, hN⟩)
  have hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0 := by
    intro v
    rw [← hWinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, id]
    constructor
    · intro hv N
      have h1 := hv N N.2
      rw [hNker N] at h1
      exact h1
    · intro h N hN
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      rw [h1]
      exact h ⟨N, hN⟩

  let Ω := AlgebraicClosure K
  have hfinKi : ∀ N, FiniteDimensional K (Ki N) := fun N =>
    Module.Finite.of_restrictScalars_finite ℚ K (Ki N)
  let ιi : ∀ N : t, Ki N →ₐ[K] Ω := fun N =>
    have := hfinKi N
    IsAlgClosed.lift
  let M : IntermediateField K Ω := ⨆ N : t, (ιi N).fieldRange
  have hMfin : FiniteDimensional K M := by
    have : ∀ N : t, FiniteDimensional K (ιi N).fieldRange := fun N =>
      haveI := hfinKi N
      (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional
    exact IntermediateField.finiteDimensional_iSup_of_finite
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hLfin : FiniteDimensional K L := inferInstance
  have hLgal : IsGalois K L := inferInstance
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hQL : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hnfL : NumberField L := ⟨⟩

  have hrange : ∀ N (x : Ki N), ιi N x ∈ L := fun N x =>
    hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)
  let e0 : ∀ N : t, Ki N →ₐ[K] L := fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)

  have hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v) :=
    fun N e => henl (Ki N) L e (fi N) (hfam N)
  choose g hgfam hgval using hg
  let gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V) :=
    fun p => (g p.1 p.2).liftBaseChange L
  have hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v := fun p v =>
    LinearMap.liftBaseChange_one_tmul _ _ _
  let Kc : Submodule L (L ⊗[K] V) := ⨅ p, LinearMap.ker (gh p)

  have hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V),
      gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x) := by
    intro σ N e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul,
        AlgHom.comp_apply]
      congr 1
      exact (σ.apply_symm_apply _).symm
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc := by
    intro σ x hx
    rw [Submodule.mem_iInf] at hx ⊢
    rintro ⟨N, e⟩
    rw [LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]
  have hGD := galoisDescent_holds K L V Kc hstab
  have hkP : kPoints Kc = W := by
    ext v
    rw [hWmem]
    show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h N
      have h1 := LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)
      have h2 : e0 N (fi N v) = 0 := by
        have h3 := hgval N (e0 N) v
        rw [← h3]
        simpa [hgh1] using h1
      exact (e0 N).toRingHom.injective (by simpa using h2)
    · intro h p
      rw [LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]
  have hKc : Kc = baseSpan L W := by rw [hGD, hkP]

  let G : Set (Module.Dual L (L ⊗[K] V)) := Set.range gh
  obtain ⟨t', ht'sub, ht'span, ht'li⟩ := exists_linearIndependent L G
  have ht'fin : t'.Finite := ht'li.setFinite
  have : Fintype t' := ht'fin.fintype
  set ρ := Fintype.card t' with hρ
  let eT := Fintype.equivFin t'
  have hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V)) :=
    fun i => ht'sub (eT.symm i).2
  choose pk hpk using hpick
  let cfL : Fin ρ → Module.Dual L (L ⊗[K] V) := fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))
  have hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc := by
    intro x
    constructor
    · intro h
      rw [Submodule.mem_iInf]
      intro p
      rw [LinearMap.mem_ker]
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun φ hφ => ?_
        have := h (eT ⟨φ, hφ⟩)
        simpa [cfL] using this
      have hmem : gh p ∈ Submodule.span L t' := ht'span ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa using hsp hmem
    · intro hx i
      rw [Submodule.mem_iInf] at hx
      show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0
      rw [← hpk i]
      exact LinearMap.mem_ker.mp (hx (pk i))
  have hcoan : (Submodule.span L t').dualCoannihilator = Kc := by
    ext x
    rw [Submodule.mem_dualCoannihilator, ← hcomm]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span (eT.symm i).2)
    · intro h φ hφ
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun ψ hψ => ?_
        have := h (eT ⟨ψ, hψ⟩)
        simpa [cfL] using this
      simpa using hsp hφ
  have hWfd : FiniteDimensional K W := inferInstance
  have hdim : Module.finrank K W + ρ = Module.finrank K V := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')
    rw [hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange] at h1
    have h2 : Module.finrank L (Submodule.span L t') = ρ := by
      rw [hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]
    omega
  refine ⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL,
    fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩
  · rw [show cfL i = gh (pk i) from (hpk i).symm, hgh1]
  · rw [hcomm, hKc]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank

open NumberField Module
open scoped TensorProduct

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem rank_quot (M₁ : Submodule R X) (hM₁ : M₁.FG) (N : Submodule F X) :
    Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
        Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
      Module.finrank F ↥(Submodule.span F (M₁ : Set X)) := by
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn

end

section
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]

theorem rank_QuotMW (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    Module.finrank (𝓞 K) (QuotMW M W) + Module.finrank K W = Module.finrank K V := by
  have h := rank_quot (F := K) M hM W
  rw [hspan, top_inf_eq, finrank_top] at h
  exact h

theorem span_tmul_one : Submodule.span K₁ (Set.range fun v : V => (1 : K₁) ⊗ₜ[K] v) = ⊤ := by
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a v =>
    have : a ⊗ₜ[K] v = a • ((1 : K₁) ⊗ₜ[K] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem tmul_mem_span {ι : Type*} (g : ι → V) {y : V} (hy : y ∈ Submodule.span K (Set.range g)) :
    (1 : K₁) ⊗ₜ[K] y ∈ Submodule.span K₁ (Set.range fun j => (1 : K₁) ⊗ₜ[K] g j) := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, rfl⟩ := hy; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul K₁ r]
    exact Submodule.smul_mem _ _ ha

theorem quot_finrank (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤) :
    finrank K₁ ((K₁ ⊗[K] V) ⧸
      Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) =
      finrank (𝓞 K) (QuotMW M W) := by
  have hρ := rank_QuotMW M hM hspan W
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have hP : finrank K₁ P ≤ finrank K W := by
    let B := Module.finBasis K W
    have hle : P ≤ Submodule.span K₁ (Set.range fun k => (1 : K₁) ⊗ₜ[K] ((B k : W) : V)) := by
      rw [hPdef, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      apply tmul_mem_span
      have h1 : (⟨a, ha⟩ : W) ∈ Submodule.span K (Set.range B) := by
        rw [B.span_eq]; trivial
      have h2 := Submodule.apply_mem_span_image_of_mem_span W.subtype h1
      rw [← Set.range_comp] at h2
      exact h2
    calc finrank K₁ P ≤ _ := Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin (finrank K W)) := finrank_range_le_card _
      _ = finrank K W := Fintype.card_fin _
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hU : finrank K₁ (K₁ ⊗[K] V) = finrank K V := Module.finrank_baseChange
  have hQ := Submodule.finrank_quotient_add_finrank P
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hle : finrank K₁ ((K₁ ⊗[K] V) ⧸ P) ≤ finrank (𝓞 K) (QuotMW M W) := by
    have h1 : finrank K₁ (Submodule.span K₁ (Set.range f)) ≤
        Fintype.card (Fin (finrank (𝓞 K) (QuotMW M W))) := finrank_range_le_card f
    rw [top_le_iff.mp hfspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  omega

theorem detCT_ne_zero (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V))) :
    detCT c θ ≠ 0 := by
  have hq := quot_finrank (K₁ := K₁) M hM hspan W θ hθ
  set P := Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)) with hPdef
  let e : Fin (finrank (𝓞 K) (QuotMW M W)) → K₁ ⊗[K] V :=
    fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)
  have htop : Submodule.span K₁ (Set.range e) ⊔ P = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W := by
      rw [hθ]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (tmul_mem_span _ hy) (Submodule.subset_span ⟨z, hz, rfl⟩)
  let f : Fin (finrank (𝓞 K) (QuotMW M W)) → (K₁ ⊗[K] V) ⧸ P := fun j => P.mkQ (e j)
  have hfspan : ⊤ ≤ Submodule.span K₁ (Set.range f) := by
    have h1 : Set.range f = P.mkQ '' Set.range e := Set.range_comp _ _
    rw [h1, Submodule.span_image, top_le_iff, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  have hli : LinearIndependent K₁ f :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hfspan (by rw [Fintype.card_fin, hq])
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hx : ∑ j, a j • e j ∈ P := by
    rw [← hc]
    intro i
    have h1 := congrFun ha i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc _ = ∑ j, c i (e j) * a j := Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := h1
  have h2 : ∑ j, a j • f j = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, ← map_smul, ← map_sum]
    exact (Submodule.Quotient.mk_eq_zero P).mpr hx
  exact ha0 (funext (Fintype.linearIndependent_iff.mp hli a h2))

end

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
end

