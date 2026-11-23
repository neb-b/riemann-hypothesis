module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraComapSpanEqTop
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.KSpan

theorem alt_mem_of_span {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {n : ℕ} (f : M [⋀^Fin n]→ₗ[K] N) (s : Set M) (hs : Submodule.span K s = ⊤) (T : Submodule K N)
    (hT : ∀ v : Fin n → M, (∀ i, v i ∈ s) → f v ∈ T) (v : Fin n → M) : f v ∈ T := by
  have key : ∀ j : ℕ, ∀ v : Fin n → M, (∀ i : Fin n, j ≤ i.val → v i ∈ s) → f v ∈ T := by
    intro j
    induction j with
    | zero => intro v hv; exact hT v fun i => hv i (Nat.zero_le _)
    | succ j ih =>
      intro v hv
      by_cases hj : j < n
      · have hmem : v ⟨j, hj⟩ ∈ Submodule.span K s := hs ▸ Submodule.mem_top
        have hall : ∀ x ∈ Submodule.span K s, f (Function.update v ⟨j, hj⟩ x) ∈ T := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            apply ih
            intro i hi
            by_cases h : i = ⟨j, hj⟩
            · rw [h, Function.update_self]; exact hx
            · rw [Function.update_of_ne h]
              apply hv
              have : i.val ≠ j := fun h' => h (Fin.ext h')
              omega
          | zero => rw [AlternatingMap.map_update_zero]; exact T.zero_mem
          | add a b _ _ ha hb => rw [AlternatingMap.map_update_add]; exact T.add_mem ha hb
          | smul r a _ ha => rw [AlternatingMap.map_update_smul]; exact T.smul_mem r ha
        simpa using hall _ hmem
      · exact ih v fun i hi => hv i (by have := i.isLt; omega)
  exact key n v fun i hi => absurd i.isLt (by omega)

end GlobalTheory.PD.KSpan

namespace GlobalTheory.PD


open KSpan in
theorem omB_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  intro k K _ _ _ B _ p W _ _ _ _ e he hr
  have hD : Submodule.span K (D k K '' (B : Set K)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have h2 : algebraMap B K b2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2
    set q := algebraMap B K b1 / algebraMap B K b2 with hqdef
    have e1 : algebraMap B K b1 = q * algebraMap B K b2 := by rw [hqdef, div_mul_cancel₀ _ h2]
    have hq : D k K q = (algebraMap B K b2)⁻¹ • (D k K (algebraMap B K b1) - q • D k K (algebraMap B K b2)) := by
      rw [e1, Derivation.leibniz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have m1 : D k K (algebraMap B K b1) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b1 : K), b1.2, rfl⟩
    have m2 : D k K (algebraMap B K b2) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b2 : K), b2.2, rfl⟩
    rw [SetLike.mem_coe, hq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
  have hS : (omB k K B p : Set (DR k K)) ⊆ ⋀[K]^p Ω[K⁄k] := by
    intro y hy
    change y ∈ Submodule.span k _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      exact Submodule.smul_mem _ b (ExteriorAlgebra.ιMulti_range K p ⟨_, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [← algebraMap_smul K r a]; exact Submodule.smul_mem _ _ ha
  have hP : ⋀[K]^p Ω[K⁄k] ≤ Submodule.span K (omB k K B p : Set (DR k K)) := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine alt_mem_of_span (ExteriorAlgebra.ιMulti K p) _ hD _ ?_ v
    intro v hv
    choose b hb hbv using hv
    apply Submodule.subset_span
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, b, hb, ?_⟩
    rw [one_smul]
    simp only [hbv]
  have hSC : (omB k K B p : Set (DR k K)) ⊆ e '' ((omB k K B p).comap (e.restrictScalars k) : Set W) := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range e := hr ▸ hS hy
    exact ⟨w, hy, rfl⟩
  rw [eq_top_iff, ← Submodule.map_le_map_iff_of_injective he, ← LinearMap.range_eq_map, hr, Submodule.map_span]
  exact hP.trans (Submodule.span_mono hSC)

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem smul_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    {b : K} (hb : b ∈ B) {y : DR k K} (hy : y ∈ omB k K B q) : b • y ∈ omB k K B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨b * c, B.mul_mem hb hc, v, hv, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul r y _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h

theorem ιMulti_D_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    (w : Fin q → B) : (ExteriorAlgebra.ιMulti K q fun j => D k K (w j : K)) ∈ omB k K B q := by
  apply Submodule.subset_span
  exact ⟨1, B.one_mem, fun j => (w j : K), fun j => (w j).2, (one_smul K _).symm⟩

theorem omB_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K,
    Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧
    ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  intro k K _ _ _ B _ _ q
  haveI : Algebra.FormallyEtale B K := .of_isLocalization (nonZeroDivisors B)
  let φ : Ω[B⁄k] →ₗ[B] Ω[K⁄k] := KaehlerDifferential.map k k B K
  have hD : ∀ x : B, φ (D k B x) = D k K (x : K) := fun x => KaehlerDifferential.map_D k k B K x
  have hφ : IsBaseChange K φ := IsBaseChange.of_equiv (tensorKaehlerEquivOfFormallyEtale k B K) fun x => by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl
  let E := GlobalTheory.exteriorPowerMapOver K q φ
  have hE : IsLocalizedModule (nonZeroDivisors B) E :=
    (isLocalizedModule_iff_isBaseChange _ K E).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ q)
  haveI : Module.Projective B (⋀[B]^q Ω[B⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective B Ω[B⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination B id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat B (⋀[B]^q Ω[B⁄k]) := inferInstance
  haveI : Module.IsTorsionFree B (⋀[B]^q Ω[B⁄k]) := Module.Flat.isTorsionFree
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors B) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[B]^q Ω[B⁄k])
      (IsRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  let e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K := ((⋀[K]^q Ω[K⁄k]).subtype.restrictScalars B) ∘ₗ E
  have hι : ∀ a : Fin q → Ω[B⁄k], e (exteriorPower.ιMulti B q a) =
      ExteriorAlgebra.ιMulti K q fun j => φ (a j) := by
    intro a
    change ((E (exteriorPower.ιMulti B q a) : ⋀[K]^q Ω[K⁄k]) : DR k K) = _
    rw [GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.ιMulti_apply_coe]
  have hιD : ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
    intro v
    rw [hι]
    simp only [hD]
  have hB : ∀ (b : B) (y : DR k K), b • y = (b : K) • y := fun b y => (algebraMap_smul K b y).symm
  refine ⟨e, Subtype.val_injective.comp hEinj, fun y => ⟨fun hy => ?_, ?_⟩, hιD⟩
  · have : omB k K B q ≤ LinearMap.range (e.restrictScalars k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      refine ⟨(⟨b, hb⟩ : B) • exteriorPower.ιMulti B q (fun j => D k B ⟨v j, hv j⟩), ?_⟩
      rw [LinearMap.restrictScalars_apply, map_smul, hιD, hB]
    obtain ⟨z, hz⟩ := this hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span B q Ω[B⁄k] (span_range_derivation k B)
    have hz : z ∈ Submodule.span B
        (⇑(exteriorPower.ιMulti B q) '' {a | Set.range a ⊆ Set.range (D k B)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k B (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [hιD]
      exact ιMulti_D_mem_omB_regForms B q w
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul b z _ h => rw [map_smul, hB]; exact smul_mem_omB_regForms B q b.2 h

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanX
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginBC

theorem ker_reduceLoc_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  intro T O _ _ _ _ _ _ A A₁ _ _ f i i₁ EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit hker
  have hψ : ∀ p : A₁[X], algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) p =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) p) :=
    fun _ => rfl
  have hC : ∀ c : A₁, algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) c =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) (C c)) := by
    intro c
    rw [IsScalarTower.algebraMap_apply A₁ (Ext f EA), IsScalarTower.algebraMap_apply A₁ A₁[X] (Ext f EA)]
    rfl
  have hlocX : locBC f i i₁ EA QA jA hcomp hj (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) =
      algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) Polynomial.X) := by
    rw [IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA), locBC_algebraMap]
    have h1 : inclE f EA (algebraMap A[X] EA Polynomial.X) =
        algebraMap A[X] (Ext f EA) Polynomial.X :=
      (Algebra.TensorProduct.includeRight : EA →ₐ[A[X]] Ext f EA).commutes _
    rw [h1, Algebra.TensorProduct.algebraMap_apply, algebraMap_polyOver, Polynomial.map_X]
    rfl
  have hpol : ∀ q : A₁[X],
      Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X})
        (algebraMap (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj) (algebraMap A₁[X] (Ext f EA) q)) =
      Ideal.Quotient.mk _ (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) (Polynomial.eval 0 q)) := by
    intro q
    rw [hC, Ideal.Quotient.eq, ← map_sub, ← map_sub, ← Polynomial.coeff_zero_eq_eval_zero]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := q)
    rw [hr, map_mul, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : (Ideal.Quotient.mk (Ideal.span {algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X}) :
        Loc₁ f i i₁ EA QA jA hcomp hj →+* _) =
      (Ideal.Quotient.mk _).comp ((algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) := by
    apply IsLocalization.ringHom_ext (ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl
    apply RingHom.ext; intro z
    simp only [RingHom.comp_apply, reduceLoc, IsLocalization.lift_eq]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul p x =>
      rw [reduce_tmul]
      dsimp only
      have hsplit : (p ⊗ₜ[A[X]] x : Ext f EA) =
          algebraMap A₁[X] (Ext f EA) p * inclE f EA x := by
        show (p ⊗ₜ[A[X]] x : Ext f EA) = (p ⊗ₜ[A[X]] (1 : EA)) * ((1 : PolyOver f) ⊗ₜ[A[X]] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      simp only [map_mul]
      congr 1
      · exact hpol p
      · rw [← locBC_algebraMap, ← locBC_algebraMap_base]
        have hmem : algebraMap EA (Localization.AtPrime QA) x -
            algebraMap A (Localization.AtPrime QA) (ρ (algebraMap EA (Localization.AtPrime QA) x)) ∈
              RingHom.ker ρ := by
          rw [RingHom.mem_ker, map_sub]
          have := congrArg (fun w => w (ρ (algebraMap EA (Localization.AtPrime QA) x))) hρA
          simp only [RingHom.comp_apply, RingHom.id_apply] at this
          rw [this, sub_self]
        rw [hker, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        rw [Ideal.Quotient.eq, ← map_sub, ← hc, map_mul, hlocX]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    have h := congrArg (fun w => w x) key
    simp only [RingHom.comp_apply, hx, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X) = 0
    rw [hψ, reduceLoc, IsLocalization.lift_eq,
      show algebraMap A₁[X] (Ext f EA) Polynomial.X = (@id (PolyOver f) Polynomial.X) ⊗ₜ[A[X]] (1 : EA)
        from rfl, reduce_tmul]
    show Polynomial.eval 0 (Polynomial.X : A₁[X]) * _ = 0
    rw [Polynomial.eval_X, zero_mul]

end GlobalTheory.KeyOriginBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFg
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add (f := _)]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCokernelToMultiplicativeGroupBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open GlobalTheory.EtC.KumCoker in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0),
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U)) := by
  intro q _ κ h0 H1 H2
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have key : ∀ {V : Scheme.{0}} (b : Sec Gm V), Sec.map qb (Sec.map (cokernel.π κ) b) = Sec.map ((q : ℤ) • 𝟙 Gm) b := by
    intro V b
    rw [← sec_map_comp, hqb, cokernel.π_desc]
  have hls : Sheaf.IsLocallySurjective (cokernel.π κ) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).2 inferInstance
  have inj : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Injective (Sec.map qb (U := U)) := by
    intro U hU
    refine (injective_iff_map_eq_zero ((qb.hom.app (op U)).hom)).2 (fun c hc => ?_)
    have hc' : Sec.map qb c = 0 := hc
    apply sec_eq_zero
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (cokernel.π κ).hom c, fun V g hg => ?_⟩
    obtain ⟨b, hb⟩ := hg
    have hb' : Sec.map (cokernel.π κ) b = Sec.res g c := hb
    have hz : Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 := by
      rw [← key, hb', ← sec_nat, hc', sec_res_zero]
    obtain ⟨a, rfl⟩ := H1 V (unit_res hU g) b hz
    rw [← hb', ← sec_map_comp, cokernel.condition, sec_map_zero]
  intro U hU
  refine ⟨inj U hU, fun b => ?_⟩
  obtain ⟨S, hS, hP⟩ := H2 U hU b
  choose c hc using hP
  let x : Presieve.FamilyOfElements ((cokernel κ).obj ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) S.arrows :=
    fun V g hg => Sec.map (cokernel.π κ) (c V g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    apply inj Z (unit_res hU (f₁ ≫ g₁))
    change Sec.map qb (Sec.res f₁ (Sec.map (cokernel.π κ) (c _ g₁ hg₁))) =
      Sec.map qb (Sec.res f₂ (Sec.map (cokernel.π κ) (c _ g₂ hg₂)))
    rw [← sec_nat, ← sec_nat, key, key, hc, hc, sec_res_comp, sec_res_comp, w]
  obtain ⟨t, ht, -⟩ := isSheaf_forget (cokernel κ) S hS x hx
  refine ⟨t, sub_eq_zero.1 (sec_eq_zero Gm _ ⟨S, hS, fun V g hg => ?_⟩)⟩
  have ht' : Sec.res g t = Sec.map (cokernel.π κ) (c V g hg) := ht g hg
  change (Gm.obj.map g.op).hom (Sec.map qb t - b) = 0
  rw [map_sub]
  change Sec.res g (Sec.map qb t) - Sec.res g b = 0
  rw [sec_nat, ht', key, hc, sub_self]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUpdateSubShearStatement
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_update_sub_shear' : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (g : (ι → ℂ) → ℂ), Measurable g → (∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v) → ∀ F : (ι → ℂ) → ℝ≥0∞, Measurable F → ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  first | exact @GlobalTheory.lintegral_update_sub_shear | exact GlobalTheory.lintegral_update_sub_shear | (intros; apply GlobalTheory.lintegral_update_sub_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstant_spec_localRing_const_bijective : ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A], Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  first | (exact @GlobalTheory.locallyConstant_spec_local_bijective) | (exact GlobalTheory.locallyConstant_spec_local_bijective) | (intros; apply GlobalTheory.locallyConstant_spec_local_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_presentation_of_etale_cover : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → LocallyOfFinitePresentation f := by
  first | (exact @GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (exact GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallySurjective_etale_baseChange : (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' := by
  first | (exact @GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (exact GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (intros; apply GlobalTheory.EtC.locallySurjective_etale_section_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximationStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  first | (exact @GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (exact GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (intros; apply GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeConnectingCocycleShortComplexDegreeZeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_connecting_cocycle_shortComplex_degree_zero : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R))
    (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
    S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
    ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
    CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc))
        (mappingCone.fst (resMap R S.f)) (zero_add 1)) =
      CohomologyClass.mk (zcomp (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)))) w (zero_add 1)) := by
  first | (exact @GlobalTheory.EtC.ConeConn.cone_connecting_class) | (exact GlobalTheory.EtC.ConeConn.cone_connecting_class) | (intros; apply GlobalTheory.EtC.ConeConn.cone_connecting_class  <;> assumption)
end

