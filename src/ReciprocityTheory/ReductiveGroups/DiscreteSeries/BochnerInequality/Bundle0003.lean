module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PositionPrependMemNoncompactPositionSubmodule

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnitB

private theorem re_inner_basis_lemma {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype ι] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (T : E →ₗ[ℂ] E)
    (hb : ∀ i, T (b i) = (lam i : ℂ) • b i) (C : ℝ) (hC : ∀ i, lam i ≤ C) (x : E) :
    RCLike.re (inner ℂ (T x) x) ≤ C * ‖x‖ ^ 2 := by
  have hx : x = ∑ i, (inner ℂ (b i) x) • b i := (b.sum_repr' x).symm
  have hTx : T x = ∑ i, (inner ℂ (b i) x * (lam i : ℂ)) • b i := by
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb, smul_smul]
  have h1 : inner ℂ (T x) x =
      ∑ i, (starRingEnd ℂ) (inner ℂ (b i) x * (lam i : ℂ)) * inner ℂ (b i) x := by
    have e : inner ℂ (T x) x = inner ℂ (∑ i, (inner ℂ (b i) x * (lam i : ℂ)) • b i)
        (∑ i, (inner ℂ (b i) x) • b i) := by
      rw [← hTx, ← hx]
    rw [e]
    exact b.orthonormal.inner_sum _ _ _
  have h2 : inner ℂ x x = ∑ i, (starRingEnd ℂ) (inner ℂ (b i) x) * inner ℂ (b i) x := by
    have e : inner ℂ x x = inner ℂ (∑ i, (inner ℂ (b i) x) • b i)
        (∑ i, (inner ℂ (b i) x) • b i) := by
      rw [← hx]
    rw [e]
    exact b.orthonormal.inner_sum _ _ _
  have hself : RCLike.re (inner ℂ x x) = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hn : ‖x‖ ^ 2 = ∑ i, Complex.normSq (inner ℂ (b i) x) := by
    rw [← hself, RCLike.re_to_complex, h2, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [h1, hn, Finset.mul_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have e3 : (starRingEnd ℂ) (inner ℂ (b i) x * (lam i : ℂ)) * inner ℂ (b i) x =
      ((lam i * Complex.normSq (inner ℂ (b i) x) : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  rw [e3, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hC i) (Complex.normSq_nonneg _)

theorem re_inner_le_of_isSymmetric_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (C : ℝ)
    (h : ∀ v : E, v ≠ 0 → ∀ θ : ℝ, T v = (θ : ℂ) • v → θ ≤ C) (x : E) :
    RCLike.re (inner ℂ (T x) x) ≤ C * ‖x‖ ^ 2 := by
  exact re_inner_basis_lemma (hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl)
    (hT.eigenvalues (n := Module.finrank ℂ E) rfl) T
    (fun i => hT.apply_eigenvectorBasis rfl i) C
    (fun i => h _ ((hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl).orthonormal.ne_zero i) _
      (hT.apply_eigenvectorBasis rfl i)) x

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem casimirK_inner_symm (hU : IsKUnitary ε A) (x y : X) :
    inner ℂ (casimirK ε A x) y = inner ℂ x (casimirK ε A y) := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [hU a b hab.symm, hU b a hab]

theorem casimirK_mem_of_kStable {S : Submodule ℂ X} (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) : casimirK ε A x ∈ S := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  exact hS a b hab.symm _ (hS b a hab _ hx)

theorem eig_casimirK (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x : X} (hx : x ∈ S) (hx0 : x ≠ 0)
    {θ : ℂ} (hθ : casimirK ε A x = θ • x) :
    ∃ w ∈ S, w ≠ 0 ∧ casimirK ε A w = θ • w ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w ∧
      θ = (casValK ε μ : ℂ) := by
  classical
  set T : Submodule ℂ X := S ⊓ LinearMap.ker (casimirK ε A - θ • (1 : Module.End ℂ X)) with hTdef
  have memT : ∀ y, y ∈ T ↔ y ∈ S ∧ casimirK ε A y = θ • y := by
    intro y
    simp only [T, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have := hfd
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
  have hTs : IsKStableSub ε A T := by
    intro a b hab y hy
    rw [memT] at hy ⊢
    refine ⟨hS a b hab y hy.1, ?_⟩
    have := congrArg (fun F : Module.End ℂ X => F y) (casimirK_comm ε hA a b hab)
    simp only [Module.End.mul_apply] at this
    rw [this, hy.2, map_smul]
  have hne : T ≠ ⊥ := by
    intro h
    have hxT : x ∈ T := (memT x).2 ⟨hx, hθ⟩
    rw [h, Submodule.mem_bot] at hxT
    exact hx0 hxT
  obtain ⟨w, hw, hw0, μ, hμ⟩ := exists_khw hA hU hTfd hTs hne
  rw [memT] at hw
  refine ⟨w, hw.1, hw0, hw.2, μ, hμ, ?_⟩
  have h1 := casimirK_khwVec ε hA hμ
  rw [hw.2] at h1
  exact smul_left_injective ℂ hw0 h1

theorem re_inner_casimirK_le (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (C : ℝ)
    (hC : ∀ w ∈ S, w ≠ 0 → ∀ μ : Fin n → ℝ, IsKHWVec ε A μ w → casValK ε μ ≤ C) :
    ∀ x ∈ S, RCLike.re (inner ℂ (casimirK ε A x) x) ≤ C * ‖x‖ ^ 2 := by
  haveI := hfd
  intro x hx
  let T : S →ₗ[ℂ] S := (casimirK ε A).restrict (fun y hy => casimirK_mem_of_kStable hS hy)
  have hTc : ∀ y : S, ((T y : S) : X) = casimirK ε A y := fun y => rfl
  have hT : T.IsSymmetric := by
    intro y z
    rw [Submodule.coe_inner, Submodule.coe_inner, hTc, hTc]
    exact casimirK_inner_symm hU _ _
  have key := re_inner_le_of_isSymmetric_eigen hT C (fun v hv0 θ hθ => by
    have hθ' : casimirK ε A v = (θ : ℂ) • (v : X) := congrArg Subtype.val hθ
    obtain ⟨w, hwS, hw0, -, μ, hkhw, hθμ⟩ := eig_casimirK hA hU hfd hS v.2
      (fun h => hv0 (Subtype.ext h)) hθ'
    have e : θ = casValK ε μ := by exact_mod_cast hθμ
    rw [e]
    exact hC w hwS hw0 μ hkhw) ⟨x, hx⟩
  rw [Submodule.coe_inner, hTc] at key
  have e1 : ((⟨x, hx⟩ : S) : X) = x := rfl
  have e2 : ‖(⟨x, hx⟩ : S)‖ = ‖x‖ := rfl
  rw [e1, e2] at key
  exact key

theorem lift_khw (hU : IsKUnitary ε A) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ a b, ε a = ε b → ∀ x, f (A a b x) = B a b (f x)) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) {x₀ : X} (hx₀ : x₀ ∈ S)
    {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (f x₀)) :
    ∃ x ∈ S, (∀ z ∈ S, f z = 0 → inner ℂ z x = 0) ∧ IsKHWVec ε A μ x ∧ f x = f x₀ := by
  classical
  haveI := hfd
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℂ X, ∀ z, z ∈ K ↔ z ∈ S ∧ f z = 0 :=
    ⟨S ⊓ LinearMap.ker f, fun z => by simp⟩
  have hKS : K ≤ S := fun z hz => ((hK z).1 hz).1
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le hKS
  obtain ⟨y, hyK, x, hxo, hsum⟩ := K.exists_add_mem_mem_orthogonal x₀
  have hyS := (hK y).1 hyK
  have hxS : x ∈ S := by
    have e : x = x₀ - y := by rw [hsum]; abel
    rw [e]
    exact S.sub_mem hx₀ hyS.1
  have hfx : f x = f x₀ := by
    rw [hsum, map_add (f := _), hyS.2, zero_add]
  have hperp : ∀ z ∈ K, inner ℂ z x = 0 := fun z hz => (Submodule.mem_orthogonal K x).1 hxo z hz
  have hKst : ∀ a b, ε a = ε b → ∀ z ∈ K, A a b z ∈ K := by
    intro a b hab z hz
    obtain ⟨hzS, hfz⟩ := (hK z).1 hz
    exact (hK _).2 ⟨hS a b hab z hzS, by rw [hf a b hab, hfz, map_zero]⟩
  have key : ∀ d, d ∈ S → f d = 0 → (∀ z ∈ K, inner ℂ z d = 0) → d = 0 := by
    intro d hdS hfd0 hdo
    exact inner_self_eq_zero.mp (hdo d ((hK d).2 ⟨hdS, hfd0⟩))
  refine ⟨x, hxS, fun z hz hfz => hperp z ((hK z).2 ⟨hz, hfz⟩),
    ⟨fun a => ?_, fun a b hab he => ?_⟩, hfx⟩
  · apply sub_eq_zero.mp
    apply key
    · exact S.sub_mem (hS a a rfl x hxS) (S.smul_mem _ hxS)
    · rw [map_sub, map_smul, hf a a rfl, hfx, hy.1 a, sub_self]
    · intro z hz
      rw [inner_sub_right, inner_smul_right, ← hU a a rfl, hperp _ (hKst a a rfl z hz),
        hperp z hz, mul_zero, sub_zero]
  · apply key
    · exact hS a b he x hxS
    · rw [hf a b he, hfx, hy.2 a b hab he]
    · intro z hz
      rw [← hU b a he.symm, hperp _ (hKst b a he.symm z hz)]

end KUnitB

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerOrth
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LayerOrth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem isKHWVec_starProjection (hU : IsKUnitary ε E) {S : Submodule ℂ M}
    [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (S.starProjection w) := by
  have hcomm : ∀ a b, ε a = ε b → ∀ v, S.starProjection (E a b v) = E a b (S.starProjection v) := by
    intro a b hab v
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS a b hab _ (S.starProjection_apply_mem v))
    intro u hu
    rw [← map_sub, hU a b hab]
    exact Submodule.inner_left_of_mem_orthogonal (hS b a hab.symm u hu)
      (Submodule.sub_starProjection_mem_orthogonal v)
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hcomm a a rfl, hw.1 a, map_smul]
  · rw [← hcomm a b he, hw.2 a b hab he, map_zero]

theorem isKHWVec_sub {μ : Fin n → ℝ} {v w : M} (hv : IsKHWVec ε E μ v)
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (v - w) := by
  refine ⟨fun a => ?_, fun a b h he => ?_⟩
  · rw [map_sub, hv.1 a, hw.1 a, smul_sub]
  · rw [map_sub, hv.2 a b h he, hw.2 a b h he, sub_zero]

theorem layer_khw_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V k) {μ : Fin n → ℝ}
    (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ ws : Fin k → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin k, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧
        (∀ u ∈ layer ε E V (j : ℕ), inner ℂ u (ws j) = 0) ∧ IsKHWVec ε E μ (ws j) := by
  have hKU : IsKUnitary ε E := by
    intro a b hab x y
    rw [hU a b x y]
    simp [adjSign, hab]
  have key : ∀ j : ℕ, ∃ p ∈ layer ε E V j, (∀ u ∈ layer ε E V j, inner ℂ u p = inner ℂ u w) ∧
      IsKHWVec ε E μ p ∧ (w ∈ layer ε E V j → p = w) := by
    intro j
    haveI := finiteDimensional_layer (ε := ε) (E := E) hVfd j
    refine ⟨(layer ε E V j).starProjection w, Submodule.starProjection_apply_mem _ _, ?_,
      isKHWVec_starProjection hKU (layer_kStable hE hVk j) hμ, ?_⟩
    · intro u hu
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu]
    · intro hw'
      exact Submodule.starProjection_eq_self_iff.mpr hw'
  choose P hP1 hP2 hP3 hP4 using key
  refine ⟨P 0, hP1 0, hP3 0, fun j => P ((j : ℕ) + 1) - P j, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [Fin.sum_univ_eq_sum_range (fun j => P (j + 1) - P j) k, Finset.sum_range_sub, hP4 k hw]
    abel
  · exact sub_mem (hP1 _) (layer_le_succ _ (hP1 _))
  · intro u hu
    rw [inner_sub_right, hP2 _ u (layer_le_succ _ hu), hP2 _ u hu, sub_self]
  · exact isKHWVec_sub (hP3 _) (hP3 _)

end LayerOrth

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.PhiPerm
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PhiPerm

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem mem_ncV_iff_apply {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem phi_apply_eq (k : ℕ) (F : Big n k M) : phi E k F = ∑ κ, word E κ (F κ) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

theorem listProd_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    (l : List (Fin n × Fin n)) {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) :
    (l.map fun p => E p.1 p.2).prod v ∈ layer ε E V (j + l.length) := by
  induction l with
  | nil => simpa using hv
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, ← add_assoc]
    exact apply_mem_layer_succ hE hV p.1 p.2 ih

theorem listProd_perm_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {l₁ l₂ : List (Fin n × Fin n)} (hp : l₁.Perm l₂) (hnc : ∀ p ∈ l₁, ε p.1 ≠ ε p.2)
    {j : ℕ} {v : M} (hv : v ∈ layer ε E V j) (m : ℕ) (hm : l₁.length ≤ m + 1) :
    (l₁.map fun p => E p.1 p.2).prod v - (l₂.map fun p => E p.1 p.2).prod v ∈
      layer ε E V (j + m) := by
  induction hp generalizing m with
  | nil => simp
  | @cons x l₁ l₂ h ih =>
    rcases m with _ | m
    · have hl1 : l₁ = [] := by simpa using hm
      subst hl1
      have hl2 := List.Perm.nil_eq h
      subst hl2
      simp
    · have hD := ih (fun p hp' => hnc p (List.mem_cons_of_mem _ hp')) m (by simpa using hm)
      have := apply_mem_layer_succ hE hV x.1 x.2 hD
      rw [map_sub] at this
      simpa [List.map_cons, List.prod_cons, Module.End.mul_apply, add_assoc] using this
  | swap x y l =>
    have hw := listProd_mem_layer hE hV l hv
    have hlen : j + l.length + 1 ≤ j + m := by simp at hm; omega
    have h1 : ∀ a b, (E a b) ((l.map fun p => E p.1 p.2).prod v) ∈ layer ε E V (j + m) :=
      fun a b => layer_mono hlen (apply_mem_layer_succ hE hV a b hw)
    have key : ((y :: x :: l).map fun p => E p.1 p.2).prod v - ((x :: y :: l).map fun p => E p.1 p.2).prod v =
        (E y.1 y.2 * E x.1 x.2 - E x.1 x.2 * E y.1 y.2) ((l.map fun p => E p.1 p.2).prod v) := by
      simp only [List.map_cons, List.prod_cons, LinearMap.sub_apply, Module.End.mul_apply]
    rw [key, hE, LinearMap.sub_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact h1 _ _
      · simp
    · split_ifs
      · exact h1 _ _
      · simp
  | trans h₁ h₂ ih₁ ih₂ =>
    have hA := ih₁ hnc m hm
    have hB := ih₂ (fun p hp' => hnc p (h₁.symm.subset hp')) m (by rw [← h₁.length_eq]; exact hm)
    have := Submodule.add_mem _ hA hB
    rwa [sub_add_sub_cancel] at this

theorem word_eq_listProd {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    word E κ = ((List.ofFn κ).map fun p => E p.1 p.2).prod := by
  rw [word, List.map_ofFn]
  rfl

theorem phi_permute_sub_mem (hE : IsGlRep E) (hV : IsKStableSub ε E V) {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) {F : Big n (k + 1) M} (hF : F ∈ ncV ε V (k + 1)) :
    phi E (k + 1) F - phi E (k + 1) (permute σ F) ∈ layer ε E V k := by
  rw [phi_apply_eq, phi_apply_eq]
  have hre : ∑ κ, word E κ ((permute σ F) κ) = ∑ κ, word E (κ ∘ σ.symm) (F κ) := by
    let e : (Fin (k + 1) → Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
      ⟨fun κ => κ ∘ σ, fun κ => κ ∘ σ.symm, fun κ => by funext i; simp, fun κ => by funext i; simp⟩
    refine Fintype.sum_equiv e _ _ (fun κ => ?_)
    show word E κ (permute σ F κ) = word E ((κ ∘ σ) ∘ σ.symm) (F (κ ∘ σ))
    have hκ : (κ ∘ σ) ∘ σ.symm = κ := by funext i; simp
    rw [hκ, permute_apply]
  rw [hre, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun κ _ => ?_)
  have hFκ := (mem_ncV_iff_apply.1 hF) κ
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · rw [if_pos hc] at hFκ
    rw [word_eq_listProd, word_eq_listProd]
    have hp : (List.ofFn κ).Perm (List.ofFn (κ ∘ σ.symm)) := (Equiv.Perm.ofFn_comp_perm σ.symm κ).symm
    have hnc : ∀ p ∈ List.ofFn κ, ε p.1 ≠ ε p.2 := fun p hp' => by
      rw [List.mem_ofFn] at hp'
      obtain ⟨i, rfl⟩ := hp'
      exact hc i
    have := listProd_perm_sub_mem hE hV hp hnc (show F κ ∈ layer ε E V 0 from hFκ) k (by simp)
    rw [zero_add] at this
    exact this
  · rw [if_neg hc] at hFκ
    rw [(Submodule.mem_bot ℂ).1 hFκ]
    simp

end PhiPerm

end ReciprocityTheory.ChartRestriction.DS
end
end

