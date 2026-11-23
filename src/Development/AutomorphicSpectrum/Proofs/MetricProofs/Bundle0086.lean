module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrame
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.SolveCoeff

private def colMat {g m : ℕ} (v : Fin m → Fin g → ℂ) : Matrix (Fin g) (Fin m) ℂ :=
  Matrix.of fun a i => v i a

private lemma colMat_eq_mul {g m : ℕ} (M f : Fin m → Fin g → ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i, f i = ∑ j, C j i • M j) : colMat f = colMat M * C := by
  ext a i
  simp only [colMat, Matrix.of_apply, Matrix.mul_apply]
  rw [h i]
  simp [Finset.sum_apply, mul_comm]

private lemma solve_eq {g m : ℕ} (A : Matrix (Fin g) (Fin m) ℂ) (C : Matrix (Fin m) (Fin m) ℂ)
    (hd : (Aᴴ * A).det ≠ 0) : (Aᴴ * A)⁻¹ * Aᴴ * (A * C) = C := by
  have hu : IsUnit (Aᴴ * A).det := isUnit_iff_ne_zero.mpr hd
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

open scoped ComplexOrder in
private lemma gram_det_ne {g m : ℕ} (M : Fin m → Fin g → ℂ) (h : LinearIndependent ℂ M) :
    ((colMat M)ᴴ * colMat M).det ≠ 0 := by
  have hinj : Function.Injective (colMat M).mulVec := by
    intro x y hxy
    have hz : ∑ i, (x - y) i • M i = 0 := by
      funext a
      have h1 : (colMat M *ᵥ (x - y)) a = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      simpa [Matrix.mulVec, dotProduct, colMat, mul_comm, Finset.sum_apply] using h1
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h _ hz i)
  have hinj2 : Function.Injective ((colMat M)ᴴ * colMat M).mulVec := by
    intro x y hxy
    apply hinj
    have h0 : ((colMat M)ᴴ * colMat M) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 := (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).1 h0
    rw [Matrix.mulVec_sub] at h1
    exact sub_eq_zero.1 h1
  have := (Matrix.mulVec_injective_iff_isUnit).1 hinj2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

private lemma cat_mul {X : Type} [TopologicalSpace X] {x : X} {l k r : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} {B : X → Matrix (Fin k) (Fin r) ℂ}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) : ContinuousAt (fun z => A z * B z) x := by
  have c : Continuous (fun p : Matrix (Fin l) (Fin k) ℂ × Matrix (Fin k) (Fin r) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact c.continuousAt.comp (hA.prodMk hB)

private lemma cat_conj {X : Type} [TopologicalSpace X] {x : X} {l k : ℕ}
    {A : X → Matrix (Fin l) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z)ᴴ) x := by
  have c : Continuous (fun N : Matrix (Fin l) (Fin k) ℂ => Nᴴ) :=
    continuous_id.matrix_conjTranspose
  exact c.continuousAt.comp hA

private lemma cat_det {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).det) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.det) := continuous_id.matrix_det
  exact c.continuousAt.comp hA

private lemma cat_adj {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    {A : X → Matrix (Fin k) (Fin k) ℂ} (hA : ContinuousAt A x) :
    ContinuousAt (fun z => (A z).adjugate) x := by
  have c : Continuous (fun N : Matrix (Fin k) (Fin k) ℂ => N.adjugate) :=
    continuous_id.matrix_adjugate
  exact c.continuousAt.comp hA

private lemma colMat_continuousAt {n g m : ℕ} (M : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (h : ∀ i, ContinuousAt (fun z => M z i) 0) : ContinuousAt (fun z => colMat (M z)) 0 := by
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_
  exact (continuous_apply a).continuousAt.comp (h i)

theorem coeff_continuous (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ)
    (T₀ : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i, ContinuousAt (fun z => M z i) 0)
    (hf : ∀ i, ContinuousAt (fun z => f z i) 0) (hli : LinearIndependent ℂ (M 0))
    (h0 : ∀ i, f 0 i = ∑ j, T₀ j i • M 0 j)
    (hspan : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) :
    ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧
      ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  have hA : ContinuousAt (fun z => colMat (M z)) 0 := colMat_continuousAt M hM
  have hF : ContinuousAt (fun z => colMat (f z)) 0 := colMat_continuousAt f hf
  have hG : ContinuousAt (fun z => (colMat (M z))ᴴ * colMat (M z)) 0 :=
    cat_mul (cat_conj hA) hA
  have hdet : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z)).det) 0 := cat_det hG
  have hd0 := gram_det_ne (M 0) hli
  have hinv : ContinuousAt (fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹) 0 := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hdet.inv₀ hd0).smul (cat_adj hG)
  refine ⟨fun z => ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z),
    cat_mul (cat_mul hinv (cat_conj hA)) hF, ?_, ?_⟩
  · show ((colMat (M 0))ᴴ * colMat (M 0))⁻¹ * (colMat (M 0))ᴴ * colMat (f 0) = T₀
    rw [colMat_eq_mul (M 0) (f 0) T₀ h0]
    exact solve_eq _ _ hd0
  · filter_upwards [hspan, hdet.eventually_ne hd0] with z hz hdz i
    have hc : ∀ i, ∃ c : Fin m → ℂ, ∑ j, c j • M z j = f z i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hz i)
    choose c hc using hc
    have hcol : colMat (f z) = colMat (M z) * Matrix.of (fun j i => c i j) :=
      colMat_eq_mul (M z) (f z) _ (fun i => by simpa using (hc i).symm)
    have hT : ((colMat (M z))ᴴ * colMat (M z))⁻¹ * (colMat (M z))ᴴ * colMat (f z)
        = Matrix.of (fun j i => c i j) := by
      rw [hcol]; exact solve_eq _ _ hdz
    simp only [hT, Matrix.of_apply]
    exact (hc i).symm

end GlobalTheory.CompanionTheory.Ar.SolveCoeff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

theorem comp_injective {s s' : E →+* ℂ}
    (h : s.comp (algebraMap (𝓞 E) E) = s'.comp (algebraMap (𝓞 E) E)) : s = s' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  exact comp_injective (RingHom.ext fun a => DFunLike.congr_fun h a)

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)

def evalHom (E : Type) [Field E] [NumberField E] : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] ((E →+* ℂ) → ℂ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _)
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    fun x y => Algebra.commutes x _

theorem evalHom_tmul (z : ℂ) (a : 𝓞 E) (s : E →+* ℂ) :
    evalHom E (z ⊗ₜ a) s = z * s (algebraMap (𝓞 E) E a) := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ ((E →+* ℂ) → ℂ))
    (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)).toIntAlgHom
    (fun x y => Algebra.commutes x _) z a
  have h2 := congrFun h s
  have h3 : (Pi.ringHom fun s : E →+* ℂ => s.comp (algebraMap (𝓞 E) E)) a s =
      s (algebraMap (𝓞 E) E a) := rfl
  simpa [evalHom, Algebra.ofId_apply, h3] using h2

theorem evalHom_surjective : Function.Surjective (evalHom E) := by
  have h : (⊤ : Submodule ℂ ((E →+* ℂ) → ℂ)) ≤ LinearMap.range (evalHom E).toLinearMap := by
    rw [← span_charVec, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨1 ⊗ₜ a, ?_⟩
    funext s
    simp [evalHom_tmul, charVec]
  intro y
  obtain ⟨t, ht⟩ := h (Submodule.mem_top (x := y))
  exact ⟨t, ht⟩

theorem evalHom_injective : Function.Injective (evalHom E) := by
  have hdim : Module.finrank ℂ (ℂ ⊗[ℤ] 𝓞 E) = Module.finrank ℂ ((E →+* ℂ) → ℂ) := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_fintype_fun_eq_card,
      NumberField.Embeddings.card]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (evalHom E).toLinearMap)).2 evalHom_surjective

def combo (c : 𝓞 E →₀ ℂ) : ℂ ⊗[ℤ] 𝓞 E := ∑ a ∈ c.support, c a ⊗ₜ a

theorem evalHom_combo (c : 𝓞 E →₀ ℂ) (s : E →+* ℂ) :
    evalHom E (combo c) s = ∑ a ∈ c.support, c a * s (algebraMap (𝓞 E) E a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [combo, map_sum, Finset.sum_apply, evalHom_tmul]


open Classical in
theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, evalHom E (combo c) = Pi.single s 1 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, ?_⟩
  funext s'
  rw [evalHom_combo, ← hc]
  simp [Finsupp.sum, Finset.sum_apply, charVec]

end Emb

section Act

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module ℂ V]

def actHom (ρ : 𝓞 E →+* Module.End ℂ V) : ℂ ⊗[ℤ] 𝓞 E →ₐ[ℂ] Module.End ℂ V :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ρ.toIntAlgHom fun x y => Algebra.commutes x (ρ y)

theorem actHom_tmul (ρ : 𝓞 E →+* Module.End ℂ V) (z : ℂ) (a : 𝓞 E) :
    actHom ρ (z ⊗ₜ a) = z • ρ a := by
  have h := Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ (Module.End ℂ V)) ρ.toIntAlgHom
    (fun x y => Algebra.commutes x (ρ y)) z a
  simpa [actHom, Algebra.ofId_apply, Algebra.smul_def] using h

theorem actHom_combo (ρ : 𝓞 E →+* Module.End ℂ V) (c : 𝓞 E →₀ ℂ) (x : V) :
    actHom ρ (combo c) x = ∑ a ∈ c.support, c a • ρ a x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [combo, map_sum, actHom_tmul, LinearMap.sum_apply]

theorem mem_eigSp_iff {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigComp_eq_combination : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V),
      (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧
        ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  intro E _ _ s₀
  classical
  choose cs hcs using exists_coeff (E := E)
  refine ⟨cs (extEmb s₀), fun V _ _ ρ => ?_⟩
  have hsum : ∑ s, combo (cs s) = 1 := by
    apply evalHom_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hcs]
    funext s'
    simp [Finset.sum_apply, Pi.single_apply]
  have hmul : ∀ (s : E →+* ℂ) (b : 𝓞 E),
      ((1 : ℂ) ⊗ₜ[ℤ] b) * combo (cs s) = s (algebraMap (𝓞 E) E b) • combo (cs s) := by
    intro s b
    apply evalHom_injective
    rw [map_mul, map_smul, hcs]
    funext s'
    by_cases h : s' = s
    · subst h
      simp [evalHom_tmul]
    · simp [evalHom_tmul, Pi.single_apply, h]
  have hsum' : ∀ x, ∑ s, actHom ρ (combo (cs s)) x = x := by
    intro x
    have h := congrArg (actHom ρ) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h
    have h2 := LinearMap.congr_fun h x
    simpa [LinearMap.sum_apply] using h2
  have heig : ∀ (s : E →+* ℂ) x, actHom ρ (combo (cs s)) x ∈ eigSp ρ (s.comp (algebraMap (𝓞 E) E)) := by
    intro s x
    refine mem_eigSp_iff.2 fun b => ?_
    have h := congrArg (actHom ρ) (hmul s b)
    rw [map_mul, map_smul, actHom_tmul, one_smul] at h
    exact LinearMap.congr_fun h x
  have hval : ∀ (s : E →+* ℂ) (σ : 𝓞 E →+* ℂ) x, x ∈ eigSp ρ σ →
      actHom ρ (combo (cs s)) x = (Pi.single s 1 : (E →+* ℂ) → ℂ) (extEmb σ) • x := by
    intro s σ x hx
    rw [actHom_combo, ← hcs s, evalHom_combo, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mem_eigSp_iff.1 hx a, smul_smul, extEmb_apply]
  have hself : ∀ x ∈ eigSp ρ s₀, actHom ρ (combo (cs (extEmb s₀))) x = x := by
    intro x hx
    rw [hval _ s₀ x hx]
    simp
  have hz : ∀ y ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ',
      actHom ρ (combo (cs (extEmb s₀))) y = 0 := by
    have hle : (⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ') ≤
        LinearMap.ker (actHom ρ (combo (cs (extEmb s₀)))) := by
      refine iSup₂_le fun σ' hσ' y hy => ?_
      rw [LinearMap.mem_ker, hval _ σ' y hy]
      have hne : extEmb σ' ≠ extEmb s₀ := fun h => hσ' (by
        rw [← extEmb_comp σ', h, extEmb_comp])
      simp [Pi.single_apply, hne]
    exact fun y hy => hle hy
  have hex : ∀ x, actHom ρ (combo (cs (extEmb s₀))) x ∈ eigSp ρ s₀ ∧
      x - actHom ρ (combo (cs (extEmb s₀))) x ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' := by
    intro x
    refine ⟨?_, ?_⟩
    · have h := heig (extEmb s₀) x
      rwa [extEmb_comp] at h
    · have e : x - actHom ρ (combo (cs (extEmb s₀))) x =
          ∑ s ∈ Finset.univ.erase (extEmb s₀), actHom ρ (combo (cs s)) x := by
        have h := hsum' x
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (extEmb s₀))] at h
        exact sub_eq_of_eq_add' h.symm
      rw [e]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hne : s.comp (algebraMap (𝓞 E) E) ≠ s₀ := fun h => (Finset.mem_erase.1 hs).1
        (comp_injective (h.trans (extEmb_comp s₀).symm))
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hne (heig s x))
  have hcomp : ∀ x, eigComp ρ s₀ x = actHom ρ (combo (cs (extEmb s₀))) x := by
    intro x
    have h : ∃ p ∈ eigSp ρ s₀, x - p ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* ℂ | σ' ≠ s₀}, eigSp ρ σ' :=
      ⟨_, (hex x).1, (hex x).2⟩
    unfold eigComp
    rw [dite_eq_left h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    have h3 := hz _ h2
    rw [map_sub, hself _ h1, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · rw [hcomp, actHom_combo]
  · rw [hcomp]
    exact (hex x).1
  · rw [hcomp, hself x hx]

end Act

end GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem oFamily_of_image : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (r : ℕ) (v : Fin r → Fin g → ℂ), I ≤ W → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) → IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) v → ∃ y : Fin r → W, (∀ a, (y a : Λ) ∈ I) ∧ (∀ a, per (y a) = v a) ∧ LinearIndependent (𝓞 E) (fun a => (y a : Λ)) ∧ (oSpan ρ v).relIndex (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) = (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup := by
  intro E _ _ g Λ _ _ W I per ρ r v hIW hinj hact hO
  classical
  set J : Submodule (𝓞 E) W := I.comap W.subtype with hJ
  have hS : AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} = J.toAddSubgroup.map per := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro p ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro p ⟨x, hx, rfl⟩
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
  rw [hS] at hO ⊢
  obtain ⟨hmem, hind, hfin⟩ := hO
  choose y hyJ hyv using fun a => (hmem a)
  have hyI : ∀ a, ((y a : W) : Λ) ∈ I := fun a => hyJ a
  have hsum : ∀ c : Fin r → 𝓞 E, per (∑ i, c i • y i) = ∑ i, ρ (c i) (v i) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hact, hyv]
  refine ⟨y, hyI, hyv, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ i, c i • y i = 0 := by
      apply Subtype.ext
      simpa using hc
    have := hind c (by rw [← hsum, h0, map_zero])
    exact congrFun this i
  · set P : Submodule (𝓞 E) W := Submodule.span (𝓞 E) (Set.range y) with hP
    have hspan : oSpan ρ v = P.toAddSubgroup.map per := by
      apply le_antisymm
      · rw [oSpan, AddSubgroup.closure_le]
        rintro p ⟨a, i, rfl⟩
        refine ⟨a • y i, ?_, ?_⟩
        · exact P.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)
        · simp only [hact, hyv]
      · rintro p ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
        show per _ ∈ _
        rw [hsum]
        exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, rfl⟩
    have hPΛ : (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup
        = P.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      have : Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ)) = P.map W.subtype := by
        rw [hP, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [this]
      ext x
      simp
    have hIΛ : I.toAddSubgroup = J.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hIW hx⟩, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [hspan, hPΛ, hIΛ, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ W.injective_subtype]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGenericTriangularFactorization
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem isGenFam_const_mul_eq_mul_upper : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_chgbasis

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoordinateTieTransferStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_dual_frame_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagTie.flagCoord_tie | exact GlobalTheory.CompanionTheory.Ar.FlagTie.flagCoord_tie | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagTie.flagCoord_tie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame <;> assumption)
end

