module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSumSubValueEqSumSqZero
section
set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationChartCoboundaryOnChartsFirstOrder
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [-instance] GlobalTheory.AdmLoc.modFun
attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartCobd

open GlobalTheory.CatCoh GlobalTheory.AnPer.Charts

theorem tsze_mul_of_fst {A : Type} [CommRing A] {n : ℕ} (x y : TrivSqZeroExt A (Fin n → A)) (hx : x.fst = 0)
    (hy : y.fst = 0) : x * y = 0 := by
  ext : 1 <;> simp [hx, hy]

theorem comap_fst_nil {A : Type} [CommRing A] {n : ℕ} (J : Ideal A) (hJ : IsNilpotent J) :
    IsNilpotent (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨N * 2, ?_⟩
  have h1 : (J.comap (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom) ^ N ≤
      RingHom.ker (TrivSqZeroExt.fstHom ℤ A (Fin n → A)).toRingHom := by
    refine (Ideal.le_comap_pow _ N).trans ?_
    rw [hN, Ideal.zero_eq_bot]
    exact le_of_eq rfl
  rw [pow_mul (M := Ideal (TrivSqZeroExt A (Fin n → A))), Ideal.zero_eq_bot, eq_bot_iff]
  refine (Ideal.pow_right_mono h1 2).trans ?_
  rw [pow_two (M := Ideal (TrivSqZeroExt A (Fin n → A))), Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  exact tsze_mul_of_fst a b ha hb

section Gen

variable {R : Type} [CommRing R] [Algebra ℂ R] {O O' : Type} [CommRing O] [Algebra ℂ O] [CommRing O'] [Algebra ℂ O']

theorem map_alg (φ : O →ₐ[ℂ] O') (r : R) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (algebraMap R (R ⊗[ℂ] O) r) = algebraMap R (R ⊗[ℂ] O') r := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem map_mem (φ : O →ₐ[ℂ] O') (M : Ideal R) (c : R ⊗[ℂ] O) (hc : c ∈ M.map (algebraMap R (R ⊗[ℂ] O))) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ c ∈ M.map (algebraMap R (R ⊗[ℂ] O')) := by
  have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom.comp (algebraMap R (R ⊗[ℂ] O)) =
      algebraMap R (R ⊗[ℂ] O') := RingHom.ext (map_alg φ)
  have := Ideal.mem_map_of_mem (Algebra.TensorProduct.map (AlgHom.id ℂ R) φ).toRingHom hc
  rwa [Ideal.map_map, e] at this

theorem map_right (φ : O →ₐ[ℂ] O') (x : O) :
    Algebra.TensorProduct.map (AlgHom.id ℂ R) φ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (φ x) := by
  simp

theorem map_nil {A : Type} [CommRing A] (f : R →+* A) (M : Ideal R) (h : IsNilpotent M) : IsNilpotent (M.map f) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

theorem lTensor_alg (D : Derivation ℂ O O) (r : R) :
    LinearMap.lTensor R D.toLinearMap (algebraMap R (R ⊗[ℂ] O) r) = 0 := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem lTensor_right (D : Derivation ℂ O O) (x : O) :
    LinearMap.lTensor R D.toLinearMap (Algebra.TensorProduct.includeRight (R := ℂ) (A := R) x) =
      Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (D x) := by
  simp

theorem right_alg (c : ℂ) : Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (algebraMap ℂ O c) =
    algebraMap R (R ⊗[ℂ] O) (algebraMap ℂ R c) := by
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tensor_subsingleton [Subsingleton O] (x y : R ⊗[ℂ] O) : x = y := Subsingleton.elim _ _

theorem fst_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)).fst = x := by simp

theorem eq_zero_of_inl_inr {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A)
    (h : (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x) : v = 0 := by
  simpa using congrArg TrivSqZeroExt.snd h

theorem inl_add_zero {A : Type} [CommRing A] {n : ℕ} (x : A) (v : Fin n → A) (h : ∀ a, v a = 0) :
    (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt A (Fin n → A)) = TrivSqZeroExt.inl x := by
  rw [show v = 0 from funext h]; simp

end Gen

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R]
  {et : Hol F₀.V →+* R} {M : Ideal R}

theorem right_cst (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) (f : Hol F₀.V) :
    Algebra.TensorProduct.includeRight (R := ℂ) (A := R) (K₀.cst k f) = algebraMap R (R ⊗[ℂ] Hol (K₀.W k)) (et f) := by
  by_cases hW : ∃ p, p ∈ K₀.W k
  · obtain ⟨p, hp⟩ := hW
    have e : K₀.cst k f = algebraMap ℂ (Hol (K₀.W k)) (f.fn p.1) := Hol.ext_fn fun p' hp' ↦ by
      rw [K₀.fn_cst k f hp', Hol.fn_algebraMap _ hp', Subsingleton.elim p'.1 p.1]
    rw [e, hev f p.1 (K₀.base k p hp)]
    exact right_alg _
  · haveI : Subsingleton (Hol (K₀.W k)) := ⟨fun a b ↦ Hol.ext_fn fun p hp ↦ (hW ⟨p, hp⟩).elim⟩
    exact tensor_subsingleton _ _

@[reducible] def objS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) (k : K₀.K) :
    K₀.DObj et M where
  T :=
    { k := k
      C := R ⊗[ℂ] Hol (K₀.W k)
      alg := ((algebraMap R (R ⊗[ℂ] Hol (K₀.W k))).comp et).toAlgebra
      J := M.map (algebraMap R (R ⊗[ℂ] Hol (K₀.W k)))
      nil := map_nil _ M hM
      ρ := (Algebra.TensorProduct.includeRight (R := ℂ) (A := R)).toRingHom
      ρ_cst := right_cst K₀ hev k }
  alg := Algebra.TensorProduct.leftAlgebra
  compat _ := rfl
  mem _ hd := Ideal.mem_map_of_mem _ hd

def homS (hM : IsNilpotent M) (hev : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) {l : Λ} {k k' : K₀.K}
    (h : K₀.le l k' k) : objS K₀ hM hev k ⟶ objS K₀ hM hev k' :=
  ⟨{ φ := letI := (objS K₀ hM hev k).T.alg; letI := (objS K₀ hM hev k').T.alg
      { (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom with commutes' := fun f ↦ map_alg (shA h) (et f) }
     deg := l
     le := h
     mem := map_mem (shA h) M
     close := by
       have e : (Algebra.TensorProduct.map (AlgHom.id ℂ R) (shA h)).toRingHom.comp (objS K₀ hM hev k).T.ρ =
           (objS K₀ hM hev k').T.ρ.comp (sh h) := RingHom.ext fun x ↦ map_right (R := R) (shA h) x
       exact Eq.mpr (congrArg (Close _ _) e) Relation.ReflTransGen.refl },
   map_alg (shA h)⟩

variable {K₀}

@[reducible] def jetD (S : K₀.DObj et M) : K₀.DObj et M where
  T :=
    { k := S.T.k
      C := TrivSqZeroExt S.T.C (Fin g → S.T.C)
      alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap (Hol F₀.V) S.T.C)).toAlgebra
      J := S.T.J.comap (TrivSqZeroExt.fstHom ℤ S.T.C (Fin g → S.T.C)).toRingHom
      nil := comap_fst_nil _ S.T.nil
      ρ := (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp S.T.ρ
      ρ_cst := fun f ↦ congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.T.ρ_cst f) }
  alg := ((TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)).comp (algebraMap R S.T.C)).toAlgebra
  compat f := congrArg (TrivSqZeroExt.inlHom S.T.C (Fin g → S.T.C)) (S.compat f)
  mem d hd := S.mem d hd

def jetHom (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hc : Close (jetD S).T.J (jetD S).T.ρ (ψ.comp S.T.ρ)) : S ⟶ jetD S :=
  ⟨{ φ := letI := (jetD S).T.alg
      { ψ with commutes' := fun f ↦ (hψ _).trans (inl_add_zero _ _ fun a ↦ by rw [S.compat]; exact hR _ a) }
     deg := 0
     le := K₀.le_refl _
     mem := fun c hc ↦ by
       change (ψ c).fst ∈ S.T.J
       rw [hψ, fst_inl_inr]; exact hc
     close := Eq.mpr (congrArg (fun ρ ↦ Close (jetD S).T.J ρ (ψ.comp S.T.ρ))
       (RingHom.ext fun x ↦ congrArg (jetD S).T.ρ (sh_refl (K₀.le_refl _) x))) hc },
   fun d ↦ (hψ _).trans (inl_add_zero _ _ (hR d))⟩

theorem killed {q : Λ →+ R} (s : ∀ S : K₀.DObj et M, S.T.C)
    (key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'), s S' - f.1.φ (s S) = algebraMap R S'.T.C (q f.1.deg))
    (S : K₀.DObj et M) (ψ : S.T.C →+* TrivSqZeroExt S.T.C (Fin g → S.T.C)) (D : S.T.C → Fin g → S.T.C)
    (hψ : ∀ x, ψ x = TrivSqZeroExt.inl x + TrivSqZeroExt.inr (D x)) (hR : ∀ r a, D (algebraMap R S.T.C r) a = 0)
    (hD : ∀ h a, D (S.T.ρ h) a = S.T.ρ (dw a h)) : D (s S) = 0 := by
  have e0 := key (jetHom S (TrivSqZeroExt.inlHom _ _) (fun _ ↦ 0) (fun x ↦ (inl_add_zero x _ fun _ ↦ rfl).symm)
    (fun _ _ ↦ rfl) Relation.ReflTransGen.refl)
  have e1 := key (jetHom S ψ D hψ hR (Relation.ReflTransGen.single
    ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ S.T.J.zero_mem, fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _,
      fun h ↦ (hψ _).trans (by
        rw [show D (S.T.ρ h) = fun a ↦ S.T.ρ (dw a h) from funext (hD h)]
        exact tsze_expand _ _)⟩))
  have e2 : ψ (s S) = TrivSqZeroExt.inl (s S) := sub_right_injective (e1.trans e0.symm)
  exact eq_zero_of_inl_inr _ _ ((hψ _).symm.trans e2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
theorem coboundary_on_charts : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →+* R) (M : Ideal R), IsNilpotent M → (∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ (q : Λ →+ R), K₀.perClD et M q = 0 → ∃ G : ∀ k, R ⊗[ℂ] Hol (K₀.W k), (∀ k a, LinearMap.lTensor R (dw a).toLinearMap (G k) = 0) ∧ ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) (G k) = q l ⊗ₜ[ℂ] 1 := by
  intro g Λ _ F₀ K₀ R _ _ et M hM hev q hq
  obtain ⟨s, hs⟩ := CatCoh.H1.mk_eq_zero.1 hq
  have key : ∀ {S S' : K₀.DObj et M} (f : S ⟶ S'),
      @HSub.hSub S'.T.C S'.T.C S'.T.C _ (s S') (f.1.φ (s S)) = algebraMap R S'.T.C (q f.1.deg) :=
    fun f ↦ congrFun (congrFun (congrFun hs _) _) f
  refine ⟨fun k ↦ s (objS K₀ hM hev k), fun k a ↦ ?_, fun l k k' h ↦ key (homS K₀ hM hev h)⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SqZeroMove.sqZeroMove (C := TrivSqZeroExt (R ⊗[ℂ] Hol (K₀.W k)) (Fin g → R ⊗[ℂ] Hol (K₀.W k))) (TrivSqZeroExt.inlHom (R ⊗[ℂ] Hol (K₀.W k)) (Fin g → R ⊗[ℂ] Hol (K₀.W k)))
    (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _)
  exact congrFun (killed s key (objS K₀ hM hev k) ψ (fun x a ↦ LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap x)
    (fun x ↦ (hψ x).trans (tsze_expand _ _).symm) (fun r a ↦ lTensor_alg _ r) (fun h a ↦ lTensor_right _ h)) a

end GlobalTheory.ChartCobd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinLogGrowthWeight
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LogGrowth

noncomputable section

theorem db_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n) (c : ℂ) :
    db n z k (fun _ => c) = fun _ => 0 := by
  funext x
  unfold db
  split_ifs <;> simp [wdb, Function.comp_def]

theorem d_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (c : ℂ) (x : M) :
    d n z j (fun _ => c) x = 0 := by
  unfold d
  split_ifs <;> simp [wd, Function.comp_def]

theorem levi_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (x : M)
    (ξ : Fin n → ℂ) : Levi n z (fun _ => c) x ξ = 0 := by
  simp only [Levi, db_const_fun, d_const_fun, zero_mul, Finset.sum_const_zero]

theorem ckR_two_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ)
    (h : SmoothR n z f) : CkR n z 2 f := fun e he => (h e he).of_le (by exact_mod_cast lse_two_le_infty)

theorem smoothR_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) :
    SmoothR n z (fun _ => c) := fun e _ => by
  simpa [Function.comp_def] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : V n => (c : ℂ)) e.target)

theorem levi_add_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) (c : ℝ)
    (hf : SmoothR n z f) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y + c) x ξ = Levi n z f x ξ := by
  have := levi_add n z f (fun _ => c) (ckR_two_of_smoothR n z f hf)
    (ckR_two_of_smoothR n z _ (smoothR_const n z c)) x ξ
  rw [this, levi_const_fun, add_zero]

theorem logShift_lse {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (X : EtaleStein n M) (k : ℕ) :
    SmoothR n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) ∧
      LeviNonneg n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsub : SmoothR n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) := by
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z X.e).1 X.smooth_e e he).add contDiffOn_const
  have h := lse n M X.z X.isLocalHomeomorph 2 0
    ![fun _ => 0, fun y => X.e y + (-Real.log ((k : ℝ) + 1))] (fun j => j.elim0) ?_ ?_
    (fun j => j.elim0) ?_
  · have hfun : (fun x => Real.log (∑ i, Real.exp ((![fun _ => (0 : ℝ), fun y => X.e y + (-Real.log ((k : ℝ) + 1))] : Fin 2 → M → ℝ) i x) +
        ∑ j : Fin 0, ‖(j.elim0 : M → ℂ) x‖ ^ 2)) =
        fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) := by
      funext x
      simp [Fin.sum_univ_two, Real.exp_add, Real.exp_neg, Real.exp_log hk, div_eq_mul_inv]
    rw [hfun] at h
    exact h
  · intro i
    fin_cases i
    · exact smoothR_const n X.z 0
    · exact hsub
  · intro i
    fin_cases i
    · intro x ξ
      simp [levi_const_fun]
    · intro x ξ
      show 0 ≤ (Levi n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) x ξ).re
      rw [levi_add_const n X.z X.e _ X.smooth_e]
      exact X.levi_e x ξ
  · intro x
    simp
    positivity

end

end GlobalTheory.LogGrowth

namespace GlobalTheory.LogGrowth

noncomputable section

theorem twisted_extension_logGrowth : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → (∃ (N : ℕ) (C : ℝ), ∀ x, -ψ x ≤ N * X.e x + C) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) φ < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGhol hΩψ hgrow hfin
  obtain ⟨N, C, hNC⟩ := hgrow
  set B : ℝ≥0∞ := 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
    ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z with hB
  by_cases hBtop : B = ⊤
  · refine ⟨fun _ => 0, fun e _ => differentiableOn_const 0, ?_⟩
    rw [hBtop]
    exact le_top
  have hBlt : B < ⊤ := lt_top_iff_ne_top.2 hBtop
  set Lk : ℕ → M → ℝ := fun k x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) with hLk
  have hL : ∀ k, SmoothR n X.z (Lk k) ∧ LeviNonneg n X.z (Lk k) := fun k => logShift_lse X k
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : ∀ k x, 0 ≤ Lk k x := by
    intro k x
    apply Real.log_nonneg
    have : 0 ≤ Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    linarith
  have hLlow : ∀ (k : ℕ) (x : M), X.e x - Real.log ((k : ℝ) + 1) ≤ Lk k x := by
    intro k x
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have ha : 0 < Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    calc X.e x - Real.log ((k : ℝ) + 1) = Real.log (Real.exp (X.e x) / ((k : ℝ) + 1)) := by
          rw [Real.log_div (Real.exp_pos _).ne' hk.ne', Real.log_exp]
      _ ≤ Lk k x := Real.log_le_log ha (by linarith)
  have hφR := (lse_smoothR_iff_real n X.z φ).1 hφ
  have hψR := (lse_smoothR_iff_real n X.z ψ).1 hψ
  have hsmk : ∀ k, SmoothR n X.z (fun x => φ x + N * Lk k x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact (hφR e he).add (contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))
  have hpk : ∀ k, SmoothR n X.z (fun x => (φ x + N * Lk k x) + ψ x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z _).1 (hsmk k) e he).add (hψR e he)
  have hstep : ∀ k : ℕ, ∃ F : M → ℂ, Holo n X.z F ∧
      ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) * Real.exp (-((φ x + N * Lk k x) + ψ x)))) ∂vol n X.z ≤ B := by
    intro k
    have hlev : ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ),
        LeviNonneg n X.z (fun x => (φ x + N * Lk k x) + α * ψ x) := by
      intro α hα x ξ
      have hfun : (fun x => (φ x + N * Lk k x) + α * ψ x) =
          fun y => (fun x => φ x + α * ψ x) y + (fun x => (N : ℝ) * Lk k x) y := by
        funext y; ring
      have hc1 : SmoothR n X.z (fun x => φ x + α * ψ x) := by
        rw [lse_smoothR_iff_real]
        intro e he
        exact (hφR e he).add (contDiffOn_const.mul (hψR e he))
      rw [hfun, levi_add n X.z (fun x => φ x + α * ψ x) (fun x => (N : ℝ) * Lk k x)
        (ckR_two_of_smoothR n X.z _ hc1)
        (ckR_two_of_smoothR n X.z _ (by
          rw [lse_smoothR_iff_real]
          intro e he
          exact contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))),
        levi_const_mul n X.z (N : ℝ) (Lk k) (ckR_two_of_smoothR n X.z _ (hL k).1)]
      rw [Complex.add_re, Complex.re_ofReal_mul]
      exact add_nonneg (hlevi α hα x ξ) (mul_nonneg hN0 ((hL k).2 x ξ))
    have hfin' : wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x)
        (fun x => (φ x + N * Lk k x) + ψ x) < ⊤ := by
      unfold wint at hfin ⊢
      have hK : ∀ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
          Real.exp (-((φ x + N * Lk k x) + ψ x))) ≤
          ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) := by
        intro x
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have h2 : (N : ℝ) * X.e x - N * Real.log ((k : ℝ) + 1) ≤ N * Lk k x := by
          have := mul_le_mul_of_nonneg_left (hLlow k x) hN0
          linarith [mul_sub (N : ℝ) (X.e x) (Real.log ((k : ℝ) + 1))]
        have h3 : Real.exp (-((φ x + N * Lk k x) + ψ x)) ≤
            Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          linarith [hNC x]
        calc ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-((φ x + N * Lk k x) + ψ x))
            ≤ ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
              (Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x)) :=
              mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = _ := by ring
      calc _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_mono hK
        _ = ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    obtain ⟨F, hF, hFle⟩ := _root_.GlobalTheory.twistedExtension_sqInt n M X (fun x => φ x + N * Lk k x) ψ G Ω δ T θ (hsmk k)
      hψ hψ0 hδ hT hθ hlev hΩ hG hGhol hΩψ hfin'
    refine ⟨F, hF, hFle.trans ?_⟩
    rw [hB]
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun x => ?_) (zero_le)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.2
    have := mul_nonneg hN0 (hL0 k x)
    linarith
  choose F hFholo hFle using hstep
  have hz := X.isLocalHomeomorph
  have hψc : Continuous ψ := by
    have h := Smooth.continuous n X.z hz _ hψ
    simpa [Function.comp_def] using Complex.continuous_re.comp h
  have hF0 := (_root_.GlobalTheory.L2Cutoff.cutoff_smooth_dbar n M X ψ G Ω δ (-T + 1) θ hψ hθ.1 hθ.2.2.1 hΩ hGhol hΩψ).1
  have hF0c := Smooth.continuous n X.z hz _ hF0
  have hden : ∀ x, 0 < 1 + min ((δ * ψ x) ^ 2) ((T + 1) ^ 2) := fun x =>
    add_pos_of_pos_of_nonneg one_pos (le_min (sq_nonneg _) (sq_nonneg _))
  have homc : Continuous (fun x => wT T (δ * ψ x)) := by
    unfold wT
    exact Continuous.div continuous_const (continuous_const.add
      (((continuous_const.mul hψc).pow 2).min continuous_const)) fun x => (hden x).ne'
  have hc : (0 : ℝ) < 1 / (1 + (T + 1) ^ 2) := by positivity
  have hbd : ∀ x, 1 / (1 + (T + 1) ^ 2) ≤ wT T (δ * ψ x) ∧ wT T (δ * ψ x) ≤ 1 := by
    intro x
    unfold wT
    constructor
    · exact one_div_le_one_div_of_le (hden x) (by linarith [min_le_right ((δ * ψ x) ^ 2) ((T + 1) ^ 2)])
    · rw [div_le_one (hden x)]
      linarith [le_min (sq_nonneg (δ * ψ x)) (sq_nonneg (T + 1))]
  have hanti : ∀ x, Antitone (fun k => (φ x + N * Lk k x) + ψ x) := by
    intro x k k' hkk
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkk' : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk 1
    have h1 : Lk k' x ≤ Lk k x := by
      apply Real.log_le_log (by have : 0 ≤ Real.exp (X.e x) / ((k' : ℝ) + 1) := by positivity
                                linarith)
      have := div_le_div_of_nonneg_left (Real.exp_pos (X.e x)).le hk hkk'
      linarith
    have := mul_le_mul_of_nonneg_left h1 hN0
    show (φ x + N * Lk k' x) + ψ x ≤ (φ x + N * Lk k x) + ψ x
    linarith
  have htend : ∀ x, Tendsto (fun k => (φ x + N * Lk k x) + ψ x) atTop (𝓝 (φ x + ψ x)) := by
    intro x
    have h1 : Tendsto (fun k : ℕ => Real.exp (X.e x) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have h2 := (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (X.e x))).comp
        (tendsto_add_atTop_nat 1)
      refine h2.congr fun k => ?_
      simp [Function.comp]
    have h3 : Tendsto (fun k : ℕ => Lk k x) atTop (𝓝 (Real.log (1 + 0))) :=
      ((Real.continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add h1)
    rw [add_zero, Real.log_one] at h3
    have h4 := ((tendsto_const_nhds (x := φ x)).add (h3.const_mul (N : ℝ))).add_const (ψ x)
    simpa using h4
  obtain ⟨Gf, hGf, hGle⟩ := _root_.GlobalTheory.holo_limit_increasing_weights n M X (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => wT T (δ * ψ x)) (1 / (1 + (T + 1) ^ 2)) (fun k x => (φ x + N * Lk k x) + ψ x)
    (fun x => φ x + ψ x) F B hF0c homc hc hbd hpk hanti htend hFholo hBlt hFle
  exact ⟨Gf, hGf, hGle⟩

end

end GlobalTheory.LogGrowth
end

