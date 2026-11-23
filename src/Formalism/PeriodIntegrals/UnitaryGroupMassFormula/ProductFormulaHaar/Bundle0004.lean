module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.BasisEApply
section
noncomputable section

open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem finrank_pos (L : LocAt F E sig p) : 0 < Module.finrank L.Fp L.Ep := by
  rw [L.rank]; norm_num

theorem nontrivial (L : LocAt F E sig p) : Nontrivial L.Ep :=
  Module.nontrivial_of_finrank_pos (finrank_pos L)

theorem finite (L : LocAt F E sig p) : Module.Finite L.Fp L.Ep :=
  Module.finite_of_finrank_pos (finrank_pos L)

theorem isUnit_ιE (L : LocAt F E sig p) {x : E} (hx : x ≠ 0) : IsUnit (L.ιE x) :=
  (isUnit_iff_ne_zero.mpr hx).map L.ιE

theorem ιE_smul (L : LocAt F E sig p) (a : F) (y : E) : L.ιE (a • y) = L.ιF a • L.ιE y := by
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]

theorem ιE_eq_sum (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) (y : E) :
    L.ιE y = ∑ i, L.ιF (b.repr y i) • L.ιE (b i) := by
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ιE_smul L _ _

theorem span_basis (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) :
    Submodule.span L.Fp (Set.range (L.ιE ∘ b)) = ⊤ := by
  rw [eq_top_iff, ← L.span, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [ιE_eq_sum L b y]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def basisE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) : Module.Basis ι L.Fp L.Ep :=
  haveI := finite L
  basisOfTopLeSpanOfCardEqFinrank (L.ιE ∘ b) (span_basis L b).ge
    (by rw [L.rank, ← h, Module.finrank_eq_card_basis b])

theorem basisE_apply (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (i : ι) : basisE L b h i = L.ιE (b i) := by
  simp [basisE]

theorem basisE_repr (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) (y : E) (i : ι) :
    (basisE L b h).repr (L.ιE y) i = L.ιF (b.repr y i) := by
  have hy : L.ιE y = ∑ j, L.ιF (b.repr y j) • basisE L b h j := by
    simp only [basisE_apply]; exact ιE_eq_sum L b y
  rw [hy, Module.Basis.repr_sum_self]

theorem leftMulMatrix_ιE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) (h : Module.finrank F E = 2) (x : E) :
    Algebra.leftMulMatrix (basisE L b h) (L.ιE x) = (Algebra.leftMulMatrix b x).map L.ιF := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    basisE_apply, ← map_mul, basisE_repr]

theorem trace_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.trace L.Fp L.Ep (L.ιE x) = L.ιF (Algebra.trace F E x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace (basisE L b h), Algebra.trace_eq_matrix_trace b,
    leftMulMatrix_ιE, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem norm_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    Algebra.norm L.Fp (L.ιE x) = L.ιF (Algebra.norm F x) := by
  classical
  let b := Module.finBasisOfFinrankEq F E h
  rw [Algebra.norm_eq_matrix_det (basisE L b h), Algebra.norm_eq_matrix_det b,
    leftMulMatrix_ιE, RingHom.map_det]
  rfl

theorem trace_tower (L : LocAt F E sig p) (y : L.Ep) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep y) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (Algebra.trace L.Fp L.Ep y)) := by
  have := L.ellPrime
  let _ : Algebra ℚ_[resChar p] L.Ep :=
    ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
  have : IsScalarTower ℚ_[resChar p] L.Fp L.Ep := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L.free
  have := finite L
  have := L.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := L.Fp) (T := L.Ep) y).symm

theorem trace_ιE_ql (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    (haveI := L.ellPrime
     letI := ((algebraMap L.Fp L.Ep).comp (algebraMap ℚ_[resChar p] L.Fp)).toAlgebra
     Algebra.trace ℚ_[resChar p] L.Ep (L.ιE x)) =
    (haveI := L.ellPrime
     Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x))) := by
  rw [trace_tower, trace_ιE L h]

theorem psiE_ιE (L : LocAt F E sig p) (h : Module.finrank F E = 2) (x : E) :
    letI := L.ellPrime
    ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
      ‖Algebra.trace ℚ_[resChar p] L.Fp (L.ιF (Algebra.trace F E x)) - (a : ℚ_[resChar p])‖ ≤ 1 ∧
      L.psiE (L.ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
  obtain ⟨a, ha, hn, he⟩ := L.psiE_def (L.ιE x)
  exact ⟨a, ha, by rwa [trace_ιE_ql L h] at hn, he⟩

end PI.ProdFormulaE.Base

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.IsOpenAddSubgroup
section
noncomputable section

open ValuativeRel

namespace PI.ProdFormulaE.ROpen

theorem isOpen_addSubgroup {G : Type*} [TopologicalSpace G] [AddCommGroup G] [ContinuousAdd G]
    (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U) (hUH : U ⊆ H) :
    IsOpen (H : Set G) := by
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset (hU.mem_nhds h0) hUH)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem isOpen_integer : IsOpen ((𝒪[F] : Subring F) : Set F) :=
  Valuation.isOpen_integer (v := ValuativeRel.valuation F)

theorem isOpen_O (L : Formalism.MainNotions.S.Loc.LocE F E) : IsOpen (L.O : Set E) := by
  classical
  haveI := L.top
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
      | (rw [IsModuleTopology.eq_moduleTopology F E]; exact ModuleTopology.continuousAdd F E)
  set b := Module.finBasis F E
  have hint : ∀ i, ∃ d : 𝒪[F], d ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E d * b i) := by
    intro i
    have halg : IsAlgebraic 𝒪[F] (b i) :=
      (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsIntegral.isIntegral (b i)).isAlgebraic
    obtain ⟨d, hd, hdi⟩ := halg.exists_integral_multiple
    exact ⟨d, hd, by simpa [Algebra.smul_def] using hdi⟩
  choose d hd0 hdi using hint
  set D : 𝒪[F] := ∏ i, d i with hD
  have hDint : ∀ i, IsIntegral 𝒪[F] (algebraMap 𝒪[F] E D * b i) := by
    intro i
    rw [hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_assoc]
    exact (isIntegral_algebraMap).mul (hdi i)
  let f : E →ₗ[F] (Fin (Module.finrank F E) → F) := b.equivFun.toLinearMap
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  let U : Set E := f ⁻¹' Set.pi Set.univ (fun _ => (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F))
  have hcont : Continuous (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) := continuous_id.mul continuous_const
  have hUo : IsOpen U := hf.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => hcont.isOpen_preimage _ isOpen_integer)
  refine isOpen_addSubgroup L.O.toAddSubgroup U hUo ?_ ?_
  · intro i _
    simp [U, f]
  · intro x hx
    have hx' : ∀ i, b.repr x i * ((D : 𝒪[F]) : F)⁻¹ ∈ 𝒪[F] := fun i => hx i (Set.mem_univ i)
    show x ∈ L.O
    rw [← b.sum_repr x]
    refine Subring.sum_mem _ fun i _ => ?_
    have hD0 : ((D : 𝒪[F]) : F) ≠ 0 := by
      rw [hD]
      push_cast
      exact Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast hd0 j
    have e : b.repr x i • b i = algebraMap 𝒪[F] E ⟨_, hx' i⟩ * (algebraMap 𝒪[F] E D * b i) := by
      rw [← mul_assoc, ← map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
      congr 2
      show b.repr x i = b.repr x i * ((D : 𝒪[F]) : F)⁻¹ * ((D : 𝒪[F]) : F)
      rw [mul_assoc, inv_mul_cancel₀ hD0, mul_one]
    rw [e]
    exact L.O.mul_mem ((L.O_def _).2 isIntegral_algebraMap) ((L.O_def _).2 (hDint i))

theorem isOpen_R [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) : IsOpen (M.R : Set E) := by
  classical
  haveI := M.L.top
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
  rcases hs : M.split with _ | g
  · have hR : M.R = M.L.O := by
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
    rw [hR]
    exact isOpen_O M.L
  · have hq0 : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h
      exact g.q_irr.ne_zero (Subtype.ext h)
    have he : Continuous g.e := IsModuleTopology.continuous_of_linearMap g.e.toLinearMap
    have hV : IsOpen ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) :=
      (continuous_id.mul continuous_const).isOpen_preimage _ isOpen_integer
    have hU : IsOpen (g.e ⁻¹' (((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) ×ˢ
        ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)))) :=
      he.isOpen_preimage _ (hV.prod hV)
    refine isOpen_addSubgroup M.R.toAddSubgroup _ hU ?_ ?_
    · simp
    · intro x hx
      obtain ⟨h1, h2⟩ := hx
      simp only [Set.mem_preimage] at h1 h2
      have m1 : (g.e x).1 ∈ 𝒪[F] := by
        have : (g.e x).1 = (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h1 (g.q).2
      have m2 : (g.e x).2 ∈ 𝒪[F] := by
        have : (g.e x).2 = (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h2 (g.q).2
      have z1 : (⟨(g.e x).1, m1⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h1⟩, Subtype.ext (by
          show (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).1
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      have z2 : (⟨(g.e x).2, m2⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h2⟩, Subtype.ext (by
          show (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).2
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      show x ∈ (M.R : Set E)
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
      rw [SetLike.mem_coe, Subring.mem_comap, Subring.mem_map]
      refine ⟨(⟨(g.e x).1, m1⟩, ⟨(g.e x).2, m2⟩), ?_, rfl⟩
      show _ = _
      show Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).1, m1⟩ : 𝒪[F]) =
        Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).2, m2⟩ : 𝒪[F])
      rw [(Ideal.Quotient.eq_zero_iff_mem).2 z1, (Ideal.Quotient.eq_zero_iff_mem).2 z2]

end PI.ProdFormulaE.ROpen

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
section
noncomputable section

open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.St

def HaarAlg : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [Module.Free K A] [Module.Finite K A] [IsModuleTopology K A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (y : A), IsUnit y → ∀ S : Set A,
      μ ((fun z => y * z) '' S) = ENNReal.ofReal (modF K (Algebra.norm K y)) * μ S

def NormLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι →
    (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ z : F, modF K (ι z) = FinitePlace.mk p z

def TrInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    (w : K), IsIntegral ℤ w → ‖Algebra.trace ℚ_[ℓ] K w‖ ≤ 1

def ResCharIff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ), ℓ.Prime →
    (resChar p = ℓ ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal))

end PI.ProdFormulaE.St

end
end

