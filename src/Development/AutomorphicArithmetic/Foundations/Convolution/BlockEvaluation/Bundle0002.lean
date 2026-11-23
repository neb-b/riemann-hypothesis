module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.FixFAnti
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {v : H} (hv : v ∈ W) : prj W v = v := by
  unfold prj
  exact Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure hv)

private theorem fixF_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {U U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (h : U' ≤ U) : fixF μ U ≤ fixF μ U' := by
  unfold fixF
  exact biInf_mono fun u hu => h hu

private theorem eig_fix {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : v ∈ V ∧ 𝔞.A v = (x : ℂ) • v ∧ v ∈ fixF μ 𝔞.U := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have h3 : 𝔞.A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 h2
  refine ⟨h1, h3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h4 := hA v
  rw [h3] at h4
  exact (Submodule.smul_mem_iff _ hx').1 h4

private theorem poly_ind {H σ ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ev : MvPolynomial σ (MvPolynomial ι ℂ) →+* (H →L[ℂ] H)) (f : MvPolynomial σ (MvPolynomial ι ℂ) →+* ℂ)
    (v : H) (s : Set σ) (h0 : ∀ c : ℂ, ev (C (C c)) v = f (C (C c)) • v)
    (h1 : ∀ i, ev (C (X i)) v = f (C (X i)) • v) (h2 : ∀ y ∈ s, ev (X y) v = f (X y) • v)
    (P : MvPolynomial σ (MvPolynomial ι ℂ)) (hP : ∀ y ∈ P.vars, y ∈ s) : ev P v = f P • v := by
  have hadd : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P + Q) v = f (P + Q) • v := by
    intro P Q hP hQ
    rw [map_add (f := _), map_add (f := _), ContinuousLinearMap.add_apply, hP, hQ, add_smul]
  have hmul : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P * Q) v = f (P * Q) • v := by
    intro P Q hP hQ
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hQ, map_smul, hP, smul_smul, mul_comm]
  have hC : ∀ c : MvPolynomial ι ℂ, ev (C c) v = f (C c) • v := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [C_add]; exact hadd _ _ hp hq
    | mul_X p i hp => rw [C_mul]; exact hmul _ _ hp (h1 i)
  have hm : P ∈ supported (MvPolynomial ι ℂ) s := mem_supported.2 fun y hy => hP y hy
  clear hP
  rw [supported_eq_adjoin_X] at hm
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact h2 y hy
  | algebraMap r => exact hC r
  | add p q _ _ hp hq => exact hadd _ _ hp hq
  | mul p q _ _ hp hq => exact hmul _ _ hp hq

private theorem eig_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) {w : Pl K} (hw : w ∉ 𝔞.S) :
    v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := by
  obtain ⟨h1, -, h2⟩ := eig_fix 𝔞 hA hx hv
  rw [Submodule.mem_inf, fixL]
  exact ⟨h1, fixF_anti μ (𝔞.max w hw) h2⟩

private theorem val_CC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (c : ℂ) : val (n := n) x Λ t (C (C c)) = c := by simp [val]

private theorem val_none {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : val (n := n) x Λ t (C (X none)) = x := by simp [val]

private theorem val_some {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (y : Ix K n) :
    val (n := n) x Λ t (C (X (some y))) = x * (Λ y.1).esymm (y.2 + 1) := by simp [val]

private theorem val_X {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (w : Pl K) (i : Fin n) :
    val (n := n) x Λ t (X (w, i)) = (t w).esymm (i + 1) := by simp [val, hval]

private theorem ev_val {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x)
    {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (h : At μ 𝔞.S V Λ t) (P : PR K n) (hPv : ∀ y ∈ P.vars, y.1 ∉ 𝔞.S) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : ev P v = val x Λ t P • v := by
  obtain ⟨hvV, hAv, hvU⟩ := eig_fix 𝔞 hA hx hv
  obtain ⟨hI, hS⟩ := h
  have hO : Oinf μ 𝔞.ν 𝔞.a₀ v = (x : ℂ) • v := by
    rw [← hAv, Amp.A, ContinuousLinearMap.comp_apply, prj_self _ hvU]
  refine poly_ind ev (val x Λ t) v {y | y.1 ∉ 𝔞.S} (fun c => ?_) (fun o => ?_) (fun y hy => ?_) P hPv
  · rw [hev.const, val_CC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  · cases o with
    | none => rw [hev.amp, hAv, val_none]
    | some y =>
      obtain ⟨-, h1⟩ := hI y.1
      rw [hev.cen, Amp.Z, ContinuousLinearMap.comp_apply, prj_self _ hvU,
        h1 𝔞.ν 𝔞.a₀ 𝔞.smooth y.2 v hvV, hO, smul_smul, mul_comm, val_some]
  · obtain ⟨w, i⟩ := y
    obtain ⟨-, -, h1⟩ := hS w hy
    rw [hev.hecke w hy i, h1 i v (eig_fixL 𝔞 hA hx hv hy), val_X]

theorem UpperTheory.ConvolutionTheory.Ci.evVal :
    EvEx → ParEx → EvVal := by
  intro hE hP K _ _ _ n hn μ _ 𝔞 V x hx hV
  obtain ⟨-, -, hA, -⟩ := hE K n hn μ 𝔞
  obtain ⟨p1, p2, -⟩ := hP K n hn μ V hV
  refine ⟨fun hne => ?_, fun Λ t Λ' t' h h' => ?_, fun ev hev Λ t h P hPv v hv => ev_val 𝔞 hA hx hev h P hPv hv⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hB : ∀ w, ∃ B, w ∉ 𝔞.S → SSat μ V w B := by
      intro w
      by_cases hw : w ∈ 𝔞.S
      · exact ⟨0, fun h => absurd hw h⟩
      · obtain ⟨B, hB⟩ := (p2 w ((Submodule.ne_bot_iff _).2 ⟨v, eig_fixL 𝔞 hA hx hv hw, hv0⟩)).exists
        exact ⟨B, fun _ => hB⟩
    choose t ht using hB
    choose Λ hΛ using fun τ => (p1 τ).exists
    exact ⟨Λ, t, And.intro hΛ ht⟩
  · refine ⟨funext fun τ => (p1 τ).unique (h.1 τ) (h'.1 τ), fun w hw => ?_⟩
    have hs := h.2 w hw
    exact (p2 w hs.2.1).unique hs (h'.2 w hw)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.HomogMonomial
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx

private noncomputable def cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R → R') (P : MvPolynomial κ R) :
    MvPolynomial κ R' := ∑ β ∈ P.support, monomial β (φ (P.coeff β))

private theorem coeff_cm {κ R R' : Type} [CommRing R] [CommRing R'] {φ : R → R'} (h0 : φ 0 = 0)
    (P : MvPolynomial κ R) (β : κ →₀ ℕ) : (cm φ P).coeff β = φ (P.coeff β) := by
  classical
  rw [cm, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, h0]

private noncomputable def sb {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) : MvPolynomial κ R →+* MvPolynomial κ' T :=
  eval₂Hom (C.comp ψ) fun x => map a (h x)

private theorem sb_monomial {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) (β : κ →₀ ℕ) (r : R) :
    sb h a ψ (monomial β r) = C (ψ r) * map a (β.prod fun i k => h i ^ k) := by
  rw [sb, eval₂Hom_monomial, map_finsuppProd]
  simp only [map_pow, RingHom.comp_apply]

private theorem cm_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R → R') (φ' : T → T') (h0 : φ 0 = 0) (h0' : φ' 0 = 0) (ha : ∀ x y, φ (x + y) = φ x + φ y)
    (ha' : ∀ x y, φ' (x + y) = φ' x + φ' y) (hl : ∀ x c, φ' (x * a c) = φ' x * a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    cm φ' (sb h a ψ P) = sb h a' ψ' (cm φ P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β r =>
    have e : cm φ (monomial β r) = monomial β (φ r) := by
      ext γ
      rw [coeff_cm h0, coeff_monomial, coeff_monomial]
      split_ifs
      · rfl
      · exact h0
    rw [e, sb_monomial, sb_monomial]
    ext γ
    rw [coeff_cm h0', coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, hl, hc]
  | add p q hp hq =>
    have e : cm φ (p + q) = cm φ p + cm φ q := by
      ext γ
      rw [MvPolynomial.coeff_add, coeff_cm h0, coeff_cm h0, coeff_cm h0, MvPolynomial.coeff_add, ha]
    rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext γ
    rw [MvPolynomial.coeff_add, coeff_cm h0', coeff_cm h0', coeff_cm h0', MvPolynomial.coeff_add, ha']

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    homog d p = ∑ α ∈ s, X none ^ (d - α.degree) * rename some (monomial α (p.coeff α)) := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα]
  simp

private theorem homog_add {ι : Type} (d : ℕ) (p q : MvPolynomial ι ℂ) : homog d (p + q) = homog d p + homog d q := by
  classical
  rw [homog_eq d _ _ support_add, homog_eq d p _ Finset.subset_union_left, homog_eq d q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), map_add (f := _), mul_add]

private theorem homog_monomial {ι : Type} (d : ℕ) (α : ι →₀ ℕ) (c : ℂ) :
    homog d (monomial α c) = X none ^ (d - α.degree) * rename some (monomial α c) := by
  classical
  rw [homog_eq d _ _ support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

private theorem homog_mul {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (c : ℂ) : homog d (p * C c) = homog d p * C c := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, mul_comm, C_mul_monomial, homog_monomial, ← C_mul_monomial, map_mul, rename_C]
    ring
  | add p q hp hq => rw [add_mul, homog_add, homog_add, hp, hq, add_mul]

private theorem homog_rename {ι ι' : Type} (δ : ι → ι') (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d (rename δ p) = rename (Option.map δ) (homog d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, map_mul, map_pow, rename_X, rename_rename]
    conv_lhs => rw [rename_monomial, homog_monomial, ← rename_monomial, rename_rename, Finsupp.degree_mapDomain]
    rfl
  | add p q hp hq => rw [map_add (f := _), homog_add, homog_add, hp, hq, map_add (f := _)]

private theorem piece_mul {ι : Type} [Fintype ι] (k : ℕ) (f : EP ι) (c : ℂ) :
    piece k (f * algebraMap ℂ (EP ι) c) = piece k f * C c := by
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, h0, zero_mul]
  | add f g hf hg => rw [add_mul, ha, ha, hf, hg, add_mul]
  | single v p =>
    have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
    rw [e, AddMonoidAlgebra.single_mul_single, add_zero, hs, hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm p, homogeneousComponent_C_mul]
    ring

private theorem lift_alg {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (c : ℂ) :
    lift x τ (algebraMap ℂ (EP ι) c) = algebraMap ℂ A c := by
  have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
  rw [e]
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem ren_ren {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] [Fintype ι''] [DecidableEq ι'] [DecidableEq ι'']
    (δ : ι → ι') (δ' : ι' → ι'') (f : EP ι) : ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

private theorem ev_ren {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (δ : ι → ι') (L : ι' → ℂ) (f : EP ι) : ev L (ren δ f) = ev (fun i => L (δ i)) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

private theorem map_eq_cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial κ R) :
    map φ P = cm φ P := by
  ext γ
  rw [coeff_map, coeff_cm (map_zero φ)]

private theorem map_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R →+* R') (φ' : T →+* T') (hl : ∀ c, φ' (a c) = a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    map φ' (sb h a ψ P) = sb h a' ψ' (map φ P) := by
  rw [map_eq_cm, map_eq_cm]
  exact cm_sb h a a' ψ ψ' φ φ' (map_zero _) (map_zero _) (map_add _) (map_add _)
    (fun x c => by rw [map_mul, hl]) hc P

theorem UpperTheory.ConvolutionTheory.Ci.kfBc :
    KfBc := by
  classical
  intro F E _ _ _ _ _ n SE SF hS Φ G hΦ hG
  let res : Ix E n → Ix F n := fun x => (x.1.comp (algebraMap F E), x.2)
  let h : Pl E × Fin n → MvPolynomial (Pl F × Fin n) ℂ := fun x =>
    rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)
  refine ⟨sb h (algebraMap ℂ _) (ren res) Φ, fun k => sb h C (rename res).toRingHom (G k), ⟨fun w => ?_, ?_⟩,
    fun k => ?_, fun d => ?_, fun L' t' ht => ?_⟩
  · have h1 := hΦ.1 fun τ => w (τ.comp (algebraMap F E))
    refine (map_sb h (algebraMap ℂ _) (algebraMap ℂ _) (ren res) (ren res)
      (ren fun x : Ix E n => (x.1, w (x.1.comp (algebraMap F E)) x.2)) _ ?_ ?_ Φ).trans (by rw [h1])
    · intro c
      exact lift_alg _ _ c
    · intro r
      rw [ren_ren, ren_ren]
      rfl
  · intro y hy
    have e : sb h (algebraMap ℂ _) (ren res) Φ =
        bind₁ (fun x => map (algebraMap ℂ (EP (Ix F n))) (h x)) (map (ren res) Φ) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [e] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    exact fun hh => hΦ.2 y' (vars_map _ _ hy') ((hS _).2 hh)
  · obtain ⟨ha, h0, -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix E n) k
    obtain ⟨ha', h0', -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix F n) k
    have h1 := hG k
    refine Eq.trans ?_ (cm_sb h (algebraMap ℂ _) C (ren res) (rename res).toRingHom (piece k) (piece k) h0 h0' ha ha'
      (piece_mul k) (fun r => UpperTheory.ConvolutionTheory.FX.piece_ren _ r _ res k) Φ).symm
    refine (map_sb h C C (rename res).toRingHom (rename res).toRingHom (aeval blockE).toRingHom _ ?_ ?_ _).trans
      (by rw [h1]; rfl)
    · intro c
      simp
    · intro r
      have e : (aeval (blockE (τ := F →+* ℂ) (n := n))).comp (rename res) =
          (rename res).comp (aeval (blockE (τ := E →+* ℂ) (n := n))) := by
        apply MvPolynomial.algHom_ext
        intro y
        simp only [AlgHom.comp_apply, rename_X, aeval_X, blockE, rename_rename]
        rfl
      exact DFunLike.congr_fun e r
  · unfold trunc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact cm_sb h C C (rename res).toRingHom (rename (Option.map res)).toRingHom (homog d) (homog d)
      (by simp [homog]) (by simp [homog]) (homog_add d) (homog_add d) (homog_mul d) (homog_rename res d) (G k)
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := Φ) (p₂ := Φ) ?_ ?_ rfl
    · refine RingHom.ext fun f => ?_
      simp only [evK, sb, RingHom.comp_apply, eval₂Hom_C]
      exact ev_ren res L' f
    · intro y hy _
      have h1 := eval_powE (resDeg F y.1) y.2 _ (ht _ fun hh => hΦ.2 y hy ((hS _).2 hh))
      simp only [evK, sb, h, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h1]
      have hc : (ev L').comp (algebraMap ℂ (EP (Ix F n))) = RingHom.id ℂ :=
        RingHom.ext fun c => lift_alg _ _ c
      rw [hc]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SepPoly
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem exists_esymm_ne {s t : Multiset ℂ} {n : ℕ} (hs : s.card = n) (ht : t.card = n) (h : s ≠ t) :
    ∃ k : Fin n, s.esymm (k + 1) ≠ t.esymm (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : s.esymm j = t.esymm j := by
      rcases j with _ | j
      · simp [Multiset.esymm]
      · exact hc ⟨j, by omega⟩
    rw [this]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem one_factor (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K))
    (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (Λ' : (K →+* ℂ) → Multiset ℂ) (t' : Pl K → Multiset ℂ)
    (h1 : ∀ τ, (Λ τ).card = n) (h2 : ∀ w ∉ S, (t w).card = n) (h3 : ∀ τ, (Λ' τ).card = n)
    (h4 : ∀ w ∉ S, (t' w).card = n) (h : ¬ (Λ = Λ' ∧ ∀ w ∉ S, t w = t' w)) :
    ∃ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ S) ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧ ∀ x : ℝ, val x Λ' t' P = 0 := by
  classical
  by_cases hΛ : Λ = Λ'
  · have : ∃ w, w ∉ S ∧ t w ≠ t' w := by
      by_contra hc
      push Not at hc
      exact h ⟨hΛ, hc⟩
    obtain ⟨w, hw, hne⟩ := this
    obtain ⟨k, hk⟩ := exists_esymm_ne (h2 w hw) (h4 w hw) hne
    refine ⟨X (w, k) - C (C ((t' w).esymm (k + 1))), ?_, ?_, ?_⟩
    · intro y hy
      have := vars_sub_subset _ hy
      rw [vars_C, vars_X, Finset.union_empty, Finset.mem_singleton] at this
      rw [this]; exact hw
    · intro x _
      simpa [val, hval, sub_eq_zero] using hk
    · intro x
      simp [val, hval]
  · obtain ⟨τ, hne⟩ := Function.ne_iff.mp hΛ
    obtain ⟨k, hk⟩ := exists_esymm_ne (h1 τ) (h3 τ) hne
    refine ⟨C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none), ?_, ?_, ?_⟩
    · intro y hy
      rw [vars_C] at hy
      exact absurd hy (Finset.notMem_empty _)
    · intro x hx
      have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have e : val x Λ t (C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none) : PR K n) =
          x * ((Λ τ).esymm (k + 1) - (Λ' τ).esymm (k + 1)) := by
        rw [val, eval₂Hom_C]
        simp
        ring
      rw [e]
      exact mul_ne_zero hx' (sub_ne_zero.mpr hk)
    · intro x
      rw [val, eval₂Hom_C]
      simp
      ring

theorem UpperTheory.ConvolutionTheory.Ci.sepPoly :
    SepPoly := by
  classical
  intro K _ _ n S Λ t I _ Λ' t' h1 h2 h3 h4 h
  choose P hP1 hP2 hP3 using fun i => one_factor K n S Λ t (Λ' i) (t' i) h1 h2 (h3 i) (h4 i) (h i)
  set Q : PR K n := ∏ i, P i with hQ
  refine ⟨Q, Q.vars.image Prod.fst, max Q.totalDegree (Q.support.sup fun β => (Q.coeff β).totalDegree), ?_,
    ⟨?_, le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_prod P hy)
    exact hP1 i y hi
  · intro y hy
    exact Finset.mem_image_of_mem _ hy
  · intro β
    by_cases hβ : β ∈ Q.support
    · exact le_max_of_le_right (Finset.le_sup (f := fun β => (Q.coeff β).totalDegree) hβ)
    · rw [notMem_support_iff.mp hβ, totalDegree_zero]
      exact Nat.zero_le _
  · intro x hx
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP2 i x hx
  · intro i x
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hP3 i x)
end

