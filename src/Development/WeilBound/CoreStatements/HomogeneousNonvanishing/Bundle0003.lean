module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib
public import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CPluri
section
namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open ReciprocityTheory.AnForm Filter Topology Set Metric Complex

theorem exists_re_of_levi_zero {e : ℕ} {d : (Fin e → ℂ) → ℝ} {c : Fin e → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ContDiffOn ℝ 2 d (ball c r)) (h0 : ∀ z ∈ ball c r, ∀ w, levi d z w = 0) :
    ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball c r) ∧ ∀ z ∈ ball c r, d z = (G z).re := by
  have hUo : IsOpen (ball c r) := isOpen_ball
  let J : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) := Complex.I • ContinuousLinearMap.id ℝ (Fin e → ℂ)
  let P : ((Fin e → ℂ) →L[ℝ] ℝ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) (Fin e → ℂ) ℝ).flip J
  have hP : ∀ (L : (Fin e → ℂ) →L[ℝ] ℝ) (w : Fin e → ℂ), P L w = L (Complex.I • w) := fun L w => rfl
  let ω : (Fin e → ℂ) → (Fin e → ℂ) →L[ℝ] ℝ := fun z => -P (fderiv ℝ d z)
  have hC : ∀ a ∈ ball c r, ContDiffAt ℝ 2 d a := fun a ha => hd.contDiffAt (hUo.mem_nhds ha)
  have hω : ∀ a ∈ ball c r, HasFDerivAt ω (-(P.comp (fderiv ℝ (fderiv ℝ d) a))) a := by
    intro a ha
    have h1 : HasFDerivAt (fderiv ℝ d) (fderiv ℝ (fderiv ℝ d) a) a :=
      (((hC a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (P.hasFDerivAt.comp a h1).neg
  have hωd : DifferentiableOn ℝ ω (ball c r) := fun a ha =>
    (hω a ha).differentiableAt.differentiableWithinAt
  have hsymm : ∀ a ∈ ball c r, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x := by
    intro a ha x y
    rw [(hω a ha).fderiv]
    have hS : IsSymmSndFDerivAt ℝ d a := (hC a ha).isSymmSndFDerivAt (by simp)
    have hL : ∀ w, fderiv ℝ (fderiv ℝ d) a w w
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • w) (Complex.I • w) = 0 := by
      intro w
      have h := h0 a ha w
      simp only [levi] at h
      linarith
    have hB : ∀ u v, fderiv ℝ (fderiv ℝ d) a u v
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • u) (Complex.I • v) = 0 := by
      intro u v
      have h1 := hL (u + v)
      have h2 := hL u
      have h3 := hL v
      simp only [smul_add, map_add (f := _), ContinuousLinearMap.add_apply] at h1
      have e1 := hS u v
      have e2 := hS (Complex.I • u) (Complex.I • v)
      linarith
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, hP]
    have k1 := hB x (Complex.I • y)
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at k1
    have k2 := hS (Complex.I • x) y
    linarith
  obtain ⟨v, hv⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric hUo hωd hsymm
  refine ⟨fun z => (d z : ℂ) + (v z : ℂ) * Complex.I, ?_, ?_⟩
  · have hO := ReciprocityTheory.AnForm.Osgood.osgood
    unfold ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
    apply hO e _ _ hUo
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hdz : HasFDerivAt d (fderiv ℝ d z) z :=
      ((hC z hz).differentiableAt (by norm_num)).hasFDerivAt
    have hG : HasFDerivAt (fun z => (d z : ℂ) + (v z : ℂ) * Complex.I)
        (Complex.ofRealCLM.comp (fderiv ℝ d z) + Complex.I • Complex.ofRealCLM.comp (ω z)) z :=
      (Complex.ofRealCLM.hasFDerivAt.comp z hdz).add
        ((Complex.ofRealCLM.hasFDerivAt.comp z (hv z hz)).mul_const Complex.I)
    rw [differentiableAt_iff_restrictScalars ℝ hG.differentiableAt]
    refine ⟨StrongDual.extendRCLike (fderiv ℝ d z), ?_⟩
    rw [hG.fderiv]
    ext w
    simp [StrongDual.extendRCLike_apply, ω, hP]
    ring
  · intro z _
    simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGSemi
section
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

open IsLocalRing Polynomial

theorem semi_complete {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsAdicComplete (maximalIdeal A) M := by
  refine
    { toIsHausdorff := inferInstance
      toIsPrecomplete := AdicCompletion.of_surjective_iff.mp ?_ }
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal A) M y
  induction t using TensorProduct.inductionOn with
  | tmul r x =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (maximalIdeal A) A r
    refine ⟨r • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion (maximalIdeal A) A) r _).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem semi_unit_or_nil {Q : Type} [CommRing Q] [Finite Q] (h : ∀ e : Q, e * e = e → e = 0 ∨ e = 1) (x : Q) :
    IsUnit x ∨ IsNilpotent x := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : Q)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have h1 : ∀ k : ℕ, x ^ (n + 1) * (x * y) ^ k = x ^ (n + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination (x * y) * ih + x * hy
  have h2 : (x * y) ^ (n + 1) * (x * y) ^ (n + 1) = (x * y) ^ (n + 1) := by
    have := h1 (n + 1)
    rw [mul_pow] at this ⊢
    linear_combination y ^ (n + 1) * this
  rcases h _ h2 with h0 | h0
  · right
    exact ⟨n + 1, by rw [← h1 (n + 1), h0, mul_zero]⟩
  · left
    exact IsUnit.of_mul_eq_one (y * (x * y) ^ n) (by rw [← h0]; ring)

theorem semi_hensel {S : Type} [CommRing S] [Nontrivial S] (I : Ideal S) [hI : HenselianRing S I] [Finite (S ⧸ I)]
    (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson hI.jac
  have hQ : ∀ e : S ⧸ I, e * e = e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
    have hm : (X ^ 2 - X : S[X]).Monic := by monicity!
    obtain ⟨a, ha, hae⟩ := hI.is_henselian (X ^ 2 - X) hm e
      (by rw [← Ideal.Quotient.eq_zero_iff_mem]; simp [pow_two, he])
      (by
        refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I e - 1) ?_
        have : (derivative (X ^ 2 - X : S[X])).eval e = 2 * e - 1 := by
          simp; norm_num
        rw [this, map_sub, map_mul, map_ofNat, map_one]
        linear_combination 4 * he)
    have ha' : a * a = a := by
      have : a ^ 2 - a = 0 := by simpa using ha
      linear_combination this
    have hae' : Ideal.Quotient.mk I a = Ideal.Quotient.mk I e := Ideal.Quotient.eq.2 hae
    rcases h a ha' with h0 | h0
    · left; rw [← hae', h0, map_zero]
    · right; rw [← hae', h0, map_one]
  have hun : ∀ x : S, IsUnit x ∨ IsNilpotent (Ideal.Quotient.mk I x) := fun x =>
    (semi_unit_or_nil hQ _).imp_left (IsUnit.of_map _ x)
  have hL : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (hun a).imp_right fun hn => IsUnit.of_map (Ideal.Quotient.mk I) _ (by
      rw [map_sub, map_one]; exact hn.isUnit_one_sub)
  have hle : I ≤ maximalIdeal S := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal S]; exact hI.jac
  have hnt : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hle))
  have hnil : ∀ x : S, IsNilpotent (Ideal.Quotient.mk I x) → x ∈ maximalIdeal S := fun x hx hu =>
    hx.not_isUnit (hu.map _)
  refine ⟨{ hL with is_henselian := ?_ }, Finite.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)⟩
  intro f hf a₀ h1 h2
  have hev : ∀ (g : S[X]) (a : S), aeval (Ideal.Quotient.mk I a) g = Ideal.Quotient.mk I (g.eval a) := fun g a =>
    aeval_algebraMap_apply_eq_algebraMap_eval a g
  obtain ⟨r, ⟨hr1, hr2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
    (P := f) (x := Ideal.Quotient.mk I a₀) (by rw [hev]; exact (hun _).resolve_left h1) (by rw [hev]; exact h2.map _)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hr : a₀ - r ∈ maximalIdeal S := hnil _ (by rw [map_sub]; exact hr1)
  have hu : IsUnit (f.derivative.eval r) := by
    by_contra hn
    have hn' : f.derivative.eval r ∈ maximalIdeal S := hn
    have h3 : f.derivative.eval a₀ - f.derivative.eval r ∈ maximalIdeal S :=
      Ideal.mem_of_dvd _ (Polynomial.sub_dvd_eval_sub _ _ _) hr
    have h4 : f.derivative.eval a₀ ∈ maximalIdeal S := by simpa using add_mem h3 hn'
    exact h4 h2
  obtain ⟨a, ha, har⟩ := hI.is_henselian f hf r (by rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev, hr2]) (hu.map _)
  refine ⟨a, ha, ?_⟩
  simpa using sub_mem (hle har) hr

theorem semi_hensel_padic (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [Nontrivial S] [Algebra ℤ_[p] S]
    [Module.Finite ℤ_[p] S] (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have h1 := semi_complete (A := ℤ_[p]) S
  have h2 : IsAdicComplete ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) S :=
    (IsAdicComplete.map_algebraMap_iff _ _).2 h1
  have h3 : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  have h4 : Module.Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have h5 : Finite (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.finite_of_finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
  exact semi_hensel ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) h

theorem semi_local (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Nontrivial R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (h : ∀ e : R, e * e = e → σ e = e → e = 0 ∨ e = 1) (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) :
    ∃ g : Matrix (Fin n) (Fin n) R, (g.map σ).transpose * A * g = 1 := by
  let S : Subalgebra ℤ_[p] R := AlgHom.equalizer σ (AlgHom.id _ _)
  have hfin : Module.Finite ℤ_[p] S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  obtain ⟨hH, hF⟩ := semi_hensel_padic p S fun e he =>
    (h e.1 (congrArg Subtype.val he) e.2).imp Subtype.ext Subtype.ext
  let τ : R ≃+* R := RingEquiv.ofBijective σ.toRingHom (Function.Involutive.bijective hσ)
  obtain ⟨g, -, hg⟩ := @Formalism.HermitianLatticesTheory.unimodUnramUnique R _ τ hσ S.toSubring (fun _ => Iff.rfl) hH hF hθ n A hA hd
  exact ⟨g, hg⟩

theorem semi_congr {Z R : Type} [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (J : Ideal R)
    (hJ : ∀ x ∈ J, σ x ∈ J) {n : ℕ} (A g g' : Matrix (Fin n) (Fin n) R) (h : ∀ i j, g i j - g' i j ∈ J) (i j : Fin n) :
    ((g.map σ).transpose * A * g) i j - ((g'.map σ).transpose * A * g') i j ∈ J := by
  have h1 : ∀ i j, Ideal.Quotient.mk J (g i j) = Ideal.Quotient.mk J (g' i j) := fun i j => Ideal.Quotient.eq.2 (h i j)
  have h2 : ∀ i j, Ideal.Quotient.mk J (σ (g i j)) = Ideal.Quotient.mk J (σ (g' i j)) := fun i j =>
    Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hJ _ (h i j))
  rw [← Ideal.Quotient.eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, h1, h2]

theorem semi_main (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) (I : Ideal R) :
    (∀ x ∈ I, σ x ∈ I) → ∃ g : Matrix (Fin n) (Fin n) R, ∀ i j,
      ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
  have hN : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[p] R
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro hI
  by_cases htop : I = ⊤
  · exact ⟨1, fun i j => htop ▸ Submodule.mem_top⟩
  by_cases he : ∃ e : R, e * e - e ∈ I ∧ σ e - e ∈ I ∧ e ∉ I ∧ 1 - e ∉ I
  · obtain ⟨e, he1, he2, he3, he4⟩ := he
    have hst : ∀ u : R, σ u - u ∈ I → ∀ x ∈ I ⊔ Ideal.span {u}, σ x ∈ I ⊔ Ideal.span {u} := by
      intro u hu x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      have : σ (a + r * u) = (σ a + σ r * (σ u - u)) + σ r * u := by rw [map_add (f := _), map_mul]; ring
      rw [this]
      exact Submodule.add_mem_sup (add_mem (hI a ha) (Ideal.mul_mem_left I _ hu)) (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)
    have hgt : ∀ u : R, u ∉ I → I < I ⊔ Ideal.span {u} := fun u hu =>
      lt_of_le_of_ne le_sup_left fun h => hu (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self u))
    have he2' : σ (1 - e) - (1 - e) ∈ I := by
      have := neg_mem he2
      rw [map_sub, map_one]
      convert this using 1
      ring
    obtain ⟨g₁, hg₁⟩ := ih _ (hgt e he3) (hst e he2)
    obtain ⟨g₂, hg₂⟩ := ih _ (hgt (1 - e) he4) (hst _ he2')
    let g : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (1 - e) * g₁ i j + e * g₂ i j
    refine ⟨g, fun i j => ?_⟩
    have k₁ := add_mem (semi_congr σ _ (hst e he2) A g g₁ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₂ i j - g₁ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₁ i j)
    have k₂ := add_mem (semi_congr σ _ (hst _ he2') A g g₂ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₁ i j - g₂ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₂ i j)
    rw [sub_add_sub_cancel] at k₁ k₂
    generalize ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j = x at k₁ k₂ ⊢
    obtain ⟨a, ha, b, hb, h1⟩ := Submodule.mem_sup.1 k₁
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨a', ha', b', hb', h2⟩ := Submodule.mem_sup.1 k₂
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    have : x = (1 - e) * a + e * a' - (r + s) * (e * e - e) := by
      linear_combination (-(1 - e)) * h1 - e * h2
    rw [this]
    exact sub_mem (add_mem (Ideal.mul_mem_left I _ ha) (Ideal.mul_mem_left I _ ha')) (Ideal.mul_mem_left I _ he1)
  · have hnt : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
    let τ : (R ⧸ I) →ₐ[ℤ_[p]] (R ⧸ I) := Ideal.quotientMapₐ I σ hI
    have hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (σ x) := fun x => rfl
    obtain ⟨g, hg⟩ := semi_local p (R ⧸ I) τ
      (fun r => by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r; rw [hτ, hτ, hσ])
      (by
        obtain ⟨θ, h⟩ := hθ
        exact ⟨Ideal.Quotient.mk I θ, by rw [hτ, ← map_sub]; exact h.map _⟩)
      (fun e h1 h2 => by
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
        by_contra hc
        rw [not_or] at hc
        refine he ⟨e, Ideal.Quotient.eq.1 h1, Ideal.Quotient.eq.1 h2, fun h => hc.1 ?_, fun h => hc.2 ?_⟩
        · exact Ideal.Quotient.eq_zero_iff_mem.2 h
        · exact (Ideal.Quotient.eq.2 h).symm)
      n (A.map (Ideal.Quotient.mk I))
      (by
        ext i j
        have := congrFun (congrFun hA i) j
        simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
        rw [hτ, this])
      (by
        have := hd.map (Ideal.Quotient.mk I)
        rwa [RingHom.map_det] at this)
    choose G hG using fun i j => Ideal.Quotient.mk_surjective (g i j)
    refine ⟨Matrix.of G, fun i j => ?_⟩
    have := congrFun (congrFun hg i) j
    rw [← Ideal.Quotient.eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      ← hG, hτ] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem tw_g_semi : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R), (∀ r, σ (σ r) = r) → (∃ θ : R, IsUnit (θ - σ θ)) → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1 := by
  intro p _ R _ _ _ σ hσ hθ n A hA hd
  obtain ⟨g, hg⟩ := semi_main p R σ hσ hθ n A hA hd ⊥ (fun x hx => by rw [Ideal.mem_bot.1 hx, map_zero]; rfl)
  have h : (g.map σ).transpose * A * g = 1 := by
    ext i j
    exact sub_eq_zero.1 (Ideal.mem_bot.1 (hg i j))
  exact ⟨g, Matrix.isUnit_det_of_left_inverse h, h⟩

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGXi
section
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem xi_den (E : Type) [Field E] [NumberField E] : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ η : E,
    (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (η * a) = z) → ∃ b : 𝓞 E, (b : E) = c * η := by
  obtain ⟨c, hc, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)).prop
  refine ⟨c, nonZeroDivisors.ne_zero hc, fun η hη => ?_⟩
  have hm : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := hη b
    exact ⟨z, hz.symm⟩
  obtain ⟨b, hb⟩ := h η hm
  exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb⟩

theorem xi_rep (E : Type) [Field E] [NumberField E] (lam : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ η : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (η * a) = lam a := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (lam (RingOfIntegers.basis E i) : ℚ)
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f, fun a => ?_⟩
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  have h : (f.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 E) E).toLinearMap
      = (Algebra.linearMap ℤ ℚ).comp lam := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    show f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [← integralBasis_apply]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun h a

theorem tw_g_xi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ ξ : E, IsCMField.complexConj E ξ = -ξ ∧ (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (ξ * a) = z) ∧ ∀ lam : 𝓞 E →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : 𝓞 E), ¬ (p : ℤ) ∣ m ∧ ∀ a : 𝓞 E, ((m * lam a : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * b * a) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨c0, hc0, hden⟩ := xi_den E
  have hbb := bar_bar bar hbar
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  set c : 𝓞 E := c0 * bar c0 with hc
  have hc' : c ≠ 0 := mul_ne_zero hc0 (by simpa using hc0)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc'
  have hcb : IsCMField.complexConj E (c : E) = c := by
    rw [← hbar, hc, map_mul, hbb, mul_comm]
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z}
      add_mem' := fun {x y} hx hy a => by
        obtain ⟨z, hz⟩ := hx a
        obtain ⟨w, hw⟩ := hy a
        exact ⟨z + w, by push_cast; rw [add_div, add_mul, map_add (f := _), hz, hw]⟩
      zero_mem' := fun a => ⟨0, by simp⟩
      smul_mem' := fun r y hy a => by
        obtain ⟨z, hz⟩ := hy (r * a)
        refine ⟨z, ?_⟩
        rw [← hz]
        congr 1
        rw [smul_eq_mul]
        push_cast
        ring }
  have hmem : ∀ y : 𝓞 E, y ∈ I ↔ ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z :=
    fun _ => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : c ∈ I := (hmem c).2 fun a => ⟨Algebra.trace ℤ (𝓞 E) a, by
      rw [div_self hcE, one_mul, Algebra.coe_trace_int]⟩
    rw [h] at this
    exact hc' this
  have hI : ∀ y ∈ I, bar y ∈ I := by
    intro y hy
    refine (hmem _).2 fun a => ?_
    obtain ⟨z, hz⟩ := (hmem y).1 hy (bar a)
    refine ⟨z, ?_⟩
    rw [← hz, ← htr ((y : E) / c * _), map_mul (IsCMField.complexConj E), map_div₀, hcb, ← hbar, ← hbar, hbb]
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨x, hxI, hx⟩ := anti_ded bar hbb I hI0 hI (tw_g_diff E bar hbar hun) (p : 𝓞 E) hp0
  have hxI' : x - bar x ∈ I := sub_mem hxI (hI x hxI)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x - bar x} := Ideal.dvd_span_singleton.2 hxI'
  have hm : ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ (m : 𝓞 E) ∈ J := by
    by_contra hne
    push Not at hne
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨Q, hJQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E)
      (Ideal.span {(p : ℤ)}) J (by
        intro m hm
        rw [Ideal.mem_span_singleton]
        by_contra h
        exact hne m h (by simpa using hm))
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQp]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp0 hpQ
    refine hx Q (hQ.isMaximal hQ0) hpQ ?_
    have : x - bar x ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self _
    rw [mul_comm Q]
    exact Ideal.mul_mono_right hJQ this
  obtain ⟨m, hmp, hmJ⟩ := hm
  refine ⟨((x - bar x : 𝓞 E) : E) / c, ?_, (hmem _).1 hxI', fun lam => ?_⟩
  · rw [map_div₀, hcb, ← hbar, map_sub, hbb]
    push_cast
    ring
  · obtain ⟨η, hη⟩ := xi_rep E lam
    obtain ⟨b, hb⟩ := hden η fun a => ⟨lam a, hη a⟩
    have hy : ((bar c0 * b : 𝓞 E) : E) / c = η := by
      rw [div_eq_iff hcE, hc]
      have e1 : ((bar c0 * b : 𝓞 E) : E) = (bar c0 : 𝓞 E) * (b : E) := rfl
      have e2 : ((c0 * bar c0 : 𝓞 E) : E) = (c0 : E) * (bar c0 : 𝓞 E) := rfl
      rw [e1, e2, hb]
      ring
    have hyI : bar c0 * b ∈ I := (hmem _).2 fun a => ⟨lam a, by rw [hy, hη]⟩
    have h2 : bar c0 * b * m ∈ Ideal.span {x - bar x} := hJ ▸ Ideal.mul_mem_mul hyI hmJ
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.1 h2
    refine ⟨m, β, hmp, fun a => ?_⟩
    have h3 : ((x - bar x : 𝓞 E) : E) / c * β * a = (m : ℚ) • (η * a) := by
      have h4 : ((bar c0 * b : 𝓞 E) : E) * m = ((x - bar x : 𝓞 E) : E) * β := by
        have := congrArg (algebraMap (𝓞 E) E) hβ
        rw [map_mul _ (bar c0 * b), map_intCast, map_mul _ _ β] at this
        exact this
      rw [← hy, Int.cast_smul_eq_zsmul, zsmul_eq_mul, div_mul_eq_mul_div, ← h4]
      ring
    rw [h3, map_smul, hη]
    simp

end PositivityTheory.UnitarySelfGeneration
end

