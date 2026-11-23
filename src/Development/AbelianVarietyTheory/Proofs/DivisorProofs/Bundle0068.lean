module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
section
open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by
  classical
  let ψ : (Fin n → Fin n → O) →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun b => Matrix.of fun i j => algebraMap O K (b i j)
      map_add' := fun b c => by ext i j; simp
      map_smul' := fun c b => by ext i j; simp [Algebra.smul_def] }
  let φ : Matrix (Fin n) (Fin n) K →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun A => a • A
      map_add' := fun A B => smul_add a A B
      map_smul' := fun c A => smul_comm a c A }
  have hφ : Function.Injective φ := fun A B hAB => smul_right_injective _ ha hAB
  have hP : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : Submodule.map φ (Subalgebra.toSubmodule (Algebra.adjoin O {g})) ≤
      LinearMap.range ψ := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    choose b hb using h k
    exact ⟨b, by ext i j; simp [ψ, φ, hb]⟩
  exact IsIntegral.of_mem_of_fg _ (Submodule.fg_of_fg_map_injective φ hφ
    (Submodule.FG.of_le_of_isNoetherian hle)) g (Algebra.self_mem_adjoin_singleton O g)

open NumberField IsDedekindDomain in
private theorem exists_smul_pow_entry_mem_adicCompletionIntegers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ (k : ℕ) (i j : Fin n),
      a * ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k) i j ∈
        w.adicCompletionIntegers E := by
  set O := w.adicCompletionIntegers E
  set C := closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))
  set S : Set (w.adicCompletion E) :=
    ⋃ i, ⋃ j, (fun h : GL (Fin n) (w.adicCompletion E) => (h : Matrix (Fin n) (Fin n) _) i j) '' C
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hg.image (Units.continuous_val.matrix_elem i j)
  let U : {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} → Set (w.adicCompletion E) :=
    fun a => (fun x => a.1 * x) ⁻¹' (O : Set _)
  have hUo : ∀ a, IsOpen (U a) := fun a =>
    (Valued.isOpen_integer _).preimage (continuous_const.mul continuous_id)
  have hcov : S ⊆ ⋃ a, U a := by
    intro x _
    by_cases hx : x ∈ O
    · exact Set.mem_iUnion.2 ⟨⟨1, O.one_mem, one_ne_zero⟩, by simpa [U] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx O.zero_mem
      have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      exact Set.mem_iUnion.2 ⟨⟨x⁻¹, hxi, inv_ne_zero hx0⟩, by simp [U, hx0, O.one_mem]⟩
  have hdir : Directed (· ⊆ ·) U := by
    rintro ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
    refine ⟨⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0⟩, ?_, ?_⟩
    · intro x hx
      have := mul_mem hb (show a * x ∈ O from hx)
      simpa [U, mul_assoc, mul_comm, mul_left_comm] using this
    · intro x hx
      have := mul_mem ha (show b * x ∈ O from hx)
      simpa [U, mul_assoc] using this
  haveI : Nonempty {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} := ⟨⟨1, O.one_mem, one_ne_zero⟩⟩
  obtain ⟨a, hSa⟩ := hS.elim_directed_cover U hUo hcov hdir
  refine ⟨a.1, a.2.2, fun k i j => hSa ?_⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨g ^ k, subset_closure ?_, by simp⟩⟩⟩
  exact Subgroup.npow_mem_zpowers g k


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    IsIntegral (w.adicCompletionIntegers E)
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_pow_entry_mem_adicCompletionIntegers E w n g hg
  exact _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded _ a ha0 fun k i j => ⟨⟨_, ha k i j⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeCharts
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory.SubschemeIntegral

theorem isPreirreducible_univ_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ a, IsOpen (U a)) (hcov : ∀ x, ∃ a, x ∈ U a) (hirr : ∀ a, IsPreirreducible (U a))
    (hmeet : ∀ a b, (U a).Nonempty → (U b).Nonempty → (U a ∩ U b).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨a, hxa⟩ := hcov x
  obtain ⟨b, hyb⟩ := hcov y
  obtain ⟨z, hza, hzu, hzb⟩ := hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩
    (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)
  obtain ⟨w, _, hw⟩ := hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩
  exact ⟨w, trivial, hw⟩

theorem fromSpec_mem_support {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (hU : IsAffineOpen U.1) (P : PrimeSpectrum Γ(Y, U.1)) (h : I.ideal U ≤ P.asIdeal) :
    hU.fromSpec P ∈ (I.support : Set Y) := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩
  change hU.fromSpec P ∈ I.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  have : hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1)) :=
    ⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩
  rw [hU.fromSpec_image_zeroLocus] at this
  exact this.1

theorem exists_cover {Y : Scheme.{0}} (I : Y.IdealSheafData) {ι : Type} (W : ι → Y.affineOpens)
    (hW : ⨆ a, (W a).1 = ⊤) (x : I.subscheme) :
    ∃ a y, (I.subschemeCover.f (W a)) y = x := by
  have hx : I.subschemeι x ∈ (⨆ a, (W a).1) := by rw [hW]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  haveI := I.subschemeCover.map_prop (W a)
  have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact ha
  obtain ⟨y, hy⟩ := this
  exact ⟨a, y, hy⟩

theorem isEmpty_spec_top {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (h : I.ideal U = ⊤) : IsEmpty (Spec (I.subschemeCover.X U)) := by
  haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h
  refine ⟨fun y => ?_⟩
  have : Subsingleton (I.subschemeCover.X U) := this
  exact y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))

theorem isIntegral_or_isEmpty_subscheme : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  intro Y I ι W hW hI hm
  by_cases hex : ∃ a, (I.ideal (W a)).IsPrime
  · left
    obtain ⟨a₀, ha₀⟩ := hex
    haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by
      intro a
      rcases hI a with h | h
      · haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
      · haveI := h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
    let 𝒰 : I.subscheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a)))
      (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))
    haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by
      change AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a))); haveI := hred a; infer_instance
    haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰
    have hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme,
        I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ := by
      intro a ha
      have := fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl
      rw [← I.range_subschemeι] at this
      exact this
    have hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a)) := by
      intro a x hx
      haveI := I.subschemeCover.map_prop (W a)
      have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
        rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact hx
      exact this
    have hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime := by
      rintro a ⟨_, y, _⟩
      rcases hI a with h | h
      · exact ((isEmpty_spec_top I (W a) h).false y).elim
      · exact h
    haveI : IrreducibleSpace I.subscheme := by
      obtain ⟨x₀, -⟩ := hpt a₀ ha₀
      have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
        refine isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_)
          (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)
        · haveI := I.subschemeCover.map_prop (W a); exact (I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range
        · obtain ⟨a, y, hy⟩ := exists_cover I W hW x; exact ⟨a, y, hy⟩
        · rcases hI a with h | h
          · haveI := isEmpty_spec_top I (W a) h
            rw [Set.range_eq_empty]; exact isPreirreducible_empty
          · haveI : IsDomain (I.subschemeCover.X (W a)) := by
              change IsDomain (Γ(Y, W a) ⧸ I.ideal (W a)); haveI := h; infer_instance
            rw [← Set.image_univ]
            exact ((IrreducibleSpace.isIrreducible_univ _).image _
              (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible
        · obtain ⟨x, hx⟩ := hpt a (hp a ha)
          refine ⟨x, hrange a x ?_, hrange b x ?_⟩
          · rw [hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]; exact ⟨_, rfl⟩
          · rw [hx]; exact hm a b (hp a ha) (hp b hb).ne_top
      haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩
      exact { toNonempty := ⟨x₀⟩ }
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · right
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, -⟩ := exists_cover I W hW x
    have h : I.ideal (W a) = ⊤ := (hI a).resolve_right (fun h => hex ⟨a, h⟩)
    exact (isEmpty_spec_top I (W a) h).false y

end GlobalTheory.SubschemeIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedAdjoin
section
namespace GlobalTheory.SepPoint

noncomputable def adjoinEquiv (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    MvPolynomial s k ≃ₐ[k] Algebra.adjoin k (s : Set F) :=
  hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))

theorem isIntegrallyClosed_adjoin (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) :
    IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := by
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (s : Set F)) :=
    (adjoinEquiv k F s hs).toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

theorem infinite_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim

theorem exists_ev (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : AlgebraicIndependent k ((↑) : s → F)) (H : Algebra.adjoin k (s : Set F)) (hH : H ≠ 0) :
    ∃ ev : Algebra.adjoin k (s : Set F) →ₐ[k] SeparableClosure k, ev H ≠ 0 := by
  haveI := infinite_of_isSepClosed (SeparableClosure k)
  let e := adjoinEquiv k F s hs
  have hP : e.symm H ≠ 0 := by simpa using hH
  obtain ⟨a, ha⟩ : ∃ a : s → SeparableClosure k,
      MvPolynomial.eval a ((e.symm H).map (algebraMap k (SeparableClosure k))) ≠ 0 := by
    by_contra! h
    apply hP
    have := MvPolynomial.funext (p := (e.symm H).map (algebraMap k (SeparableClosure k)))
      (q := 0) (fun x => by simp [h x])
    exact MvPolynomial.map_injective _ (algebraMap k (SeparableClosure k)).injective
      (by simpa using this)
  refine ⟨(MvPolynomial.aeval a).comp e.symm.toAlgHom, ?_⟩
  simpa [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval_map] using ha

end GlobalTheory.SepPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfForallDivPowTwelve
section
open IsDedekindDomain WeierstrassCurve

namespace GlobalTheory

theorem isMinimal_of_forall_div_pow_twelve (R F : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve F) (hI : W.IsIntegral R)
    (h : ∀ x : R, x ≠ 0 → W.Δ / algebraMap R F x ^ 12 ∈ (algebraMap R F).range → IsUnit x) :
    W.IsMinimal R := by
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have hC' : (C • W).IsIntegral R := hC
  rw [← Subtype.coe_le_coe]
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral]
  set v := HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hle : ∀ r : R, v (algebraMap R F r) ≤ 1 := fun r =>
    HeightOneSpectrum.valuation_le_one (K := F) (IsDiscreteValuationRing.maximalIdeal R) r
  rw [variableChange_Δ, map_mul, map_pow]
  refine mul_le_of_le_one_left' (pow_le_one' ?_ _)
  rcases ValuationRing.isInteger_or_isInteger R (C.u : F) with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact C.u.ne_zero (by simpa using hx.symm)
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R (C • W)
    have hu : IsUnit x := h x hx0 ⟨r, by
      rw [hr, variableChange_Δ, hx, Units.val_inv_eq_inv_val, inv_pow, div_eq_inv_mul]⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have : ((C.u⁻¹ : Fˣ) : F) = algebraMap R F y := by
      rw [Units.val_inv_eq_inv_val, ← hx]
      exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, hy, map_one])).symm
    rw [this]
    exact hle y
  · rw [Units.val_inv_eq_inv_val, ← hx]
    exact hle x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom
section
namespace GlobalTheory

open CommRing

theorem natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by
  have h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B') := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Submodule.one_le.mp le_rfl
  have key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'),
      ((n : B') * x) * y ∈ (I : Submodule B B') := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)
    · obtain ⟨b, hb⟩ := hn (x * j)
      have : (n : B') * x * (j * i) = b • i := by
        rw [Algebra.smul_def, hb]; ring
      rw [this]; exact Submodule.smul_mem _ b hi
    · rw [mul_add]; exact Submodule.add_mem _ hy hz
  simpa using key 1 h1

theorem finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by
  set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef
  haveI : NeZero n := ⟨hn0⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv
  haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  haveI : Finite (Submodule ℤ (B' ⧸ C)) :=
    Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective
  have hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ := by
    intro I
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : (k * n : ℤ) • x = (n : B') * (k • x) := by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
    rw [Submodule.restrictScalars_mem, this]
    exact natCast_mul_mem_units_submodule n hn I _
  let f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C) := fun I =>
    Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)
  refine Finite.of_injective f fun I J h => ?_
  have hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ := by
    have := congrArg (Submodule.comap C.mkQ) h
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)] at this
  exact Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)

theorem isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  intro B B' _ _ _ φ n hφ hn0 hn M hM
  letI : Algebra B B' := φ.toAlgebra
  haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ
  haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')
  obtain ⟨k, hk, hpow⟩ := hM.exists_pow_eq_one
  have e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B' :=
    CommRing.Pic.mapRingHom_algebraMap
  have hmem : M ^ k ∈ CommRing.relPic B B' := by
    rw [CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]; exact hpow
  rw [← Submodule.range_unitsToPic] at hmem
  obtain ⟨I, hI⟩ := hmem
  have hfo : IsOfFinOrder (M ^ k) := by
    rw [← hI]; exact (Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)
  obtain ⟨m, hm, hm1⟩ := hfo.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  set C := connectedComponent y
  have key : ∀ t, t ∉ C → irreducibleComponent t ⊆ Cᶜ := by
    intro t ht s hs hsC
    have h1 : irreducibleComponent t ⊆ connectedComponent s :=
      _root_.IsPreconnected.subset_connectedComponent
        (isIrreducible_irreducibleComponent (x := t)).isConnected.isPreconnected hs
    rw [← connectedComponent_eq hsC] at h1
    exact ht (h1 mem_irreducibleComponent)
  have hC : Cᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents Y | Z ⊆ Cᶜ}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t, key t ht⟩
      mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨-, hZ⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact hZ htZ
  have hcl : IsClosed Cᶜ := by
    rw [hC]
    exact (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  exact isClosed_compl_iff.1 hcl

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToNormalization
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.NormalizationOpenImmersion

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j) : IsOpenImmersion c.toNormalization := by
  have : IsImmersion (c ≫ p) := h ▸ inferInstance
  have : IsImmersion c := IsImmersion.of_comp c p
  infer_instance

theorem main : ∀ {V P X : AlgebraicGeometry.Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j), IsOpenImmersion c.toNormalization :=
  fun c p _ j _ _ _ h => isOpenImmersion_toNormalization c p j h

end GlobalTheory.NormalizationOpenImmersion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_snd_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hG U
  have hs : Smooth (pullback.snd G.hom G.hom) := inferInstance
  have ho : UniversallyOpen (pullback.snd G.hom G.hom) := UniversallyOpen.of_flat _
  have hmap : IsOpenMap (snd G G).left := (pullback.snd G.hom G.hom).isOpenMap
  have hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left)) :=
    ((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)
  convert hmap _ hW using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩

end GlobalTheory.IdCompOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
section
noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

def krylov {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => Matrix.mulVec (y ^ (j : ℕ)) e i

theorem krylov_apply {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) (i j : Fin r) :
    krylov y e i j = Matrix.mulVec (y ^ (j : ℕ)) e i := rfl

end GlobalTheory.LeviDesc.Krylov
end
end

