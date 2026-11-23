module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTowerStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ApproxRoot p v (Fix Ω (⨅ n, Gn T n)) := by
  first | exact @GlobalTheory.K5.TopRoots.approxRoot_fix_tower | exact GlobalTheory.K5.TopRoots.approxRoot_fix_tower | (intros; apply GlobalTheory.K5.TopRoots.approxRoot_fix_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.coef_of_inv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  intro Ω _ _ ε X l _ _ N w b c hb γ _ hinv
  obtain ⟨hslP, -, -, hev, -⟩ := mon_expand ℤ_[l] w
  have hk : ∀ (u : Fin 2 → ℤ_[l]) (k : Fin (w + 1)),
      (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 ^ (k : ℕ) * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 ^ (w - (k : ℕ)) =
        ∑ i, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) * (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) := by
    intro u k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hev, mZl, ← Betti.eval_slP, hslP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hev]
  have key : ∀ u : Fin 2 → ℤ_[l], b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) •
      ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
    intro u
    rw [← congrFun hinv u]
    show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Betti.toGQ_sl, hb, map_sum]
    simp_rw [map_smul, hk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hz := GlobalTheory.homogeneous_poly_coeff_eq_zero l (X.Khat l)
    (fun a x ha hx => GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree Ω ε X l a x ha hx) w
    (fun i => c i - ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
    (by intro u; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← hb u, ← key u, sub_self])
  intro i
  exact sub_eq_zero.1 (congrFun hz i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContCohomologyTransportMulEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem dn_comp_monoidHom {R Γ Γ' M : Type*} [CommRing R] [Group Γ] [Group Γ'] [AddCommGroup M]
    [Module R M] (φ : Γ' →* Γ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (h : ∀ g m, ρ' g m = ρ (φ g) m) (n : ℕ) (f : (Fin n → Γ) → M) (g : Fin (n + 1) → Γ') :
    dn ρ' n (fun x => f (fun i => φ (x i))) g = dn ρ n f (fun i => φ (g i)) := by
  show ρ' (g 0) (f fun i => φ (g i.succ)) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (fun i => φ (Fin.contractNth j (· * ·) g i))) =
    ρ (φ (g 0)) (f fun i => φ (g i.succ)) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) fun i => φ (g i))
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  exact Fin.comp_contractNth (· * ·) (· * ·) (map_mul φ) j g

theorem contCohomology_transport_mulEquiv :
    ∀ (R : Type) [CommRing R] (Γ Γ' : Type) [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (e : Γ' ≃* Γ), Continuous e → Continuous e.symm → ∀ (ρ : Representation R Γ M) (ρ' : Representation R Γ' M), (∀ g m, ρ' g m = ρ (e g) m) → Nonempty (H1 ρ ≃ H1 ρ') ∧ Nonempty (H2 ρ ≃ H2 ρ') ∧ (Subsingleton (Hn ρ 3) → Subsingleton (Hn ρ' 3)) := by
  intro R _ Γ Γ' _ _ _ _ M _ _ _ _ e he he' ρ ρ' h
  have h' : ∀ g m, ρ g m = ρ' (e.symm g) m := fun g m => by rw [h, e.apply_symm_apply]
  refine ⟨⟨⟨pairH1DecompositionMap ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      pairH1DecompositionMap ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩,
    ⟨⟨compatiblePairH2 ρ ρ' e.toMonoidHom he LinearMap.id continuous_id (fun g m => (h g m).symm),
      compatiblePairH2 ρ' ρ e.symm.toMonoidHom he' LinearMap.id continuous_id (fun g m => (h' g m).symm),
      ?_, ?_⟩⟩, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.apply_symm_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (e.symm_apply_apply g)
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.apply_symm_apply g.1) (e.apply_symm_apply g.2))
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      exact congrArg f.1 (Prod.ext (e.symm_apply_apply g.1) (e.symm_apply_apply g.2))
  · intro hs
    rw [GlobalTheory.Published.subsingleton_Hn_succ_iff] at hs ⊢
    intro f hf hd
    obtain ⟨c, hc, hcf⟩ := hs (fun x => f (fun i => e.symm (x i)))
      (hf.comp (continuous_pi fun i => he'.comp (continuous_apply i))) (by
        funext g
        have := dn_comp_monoidHom e.symm.toMonoidHom ρ' ρ h' 3 f g
        rw [hd] at this
        exact this)
    refine ⟨fun x => c (fun i => e (x i)),
      hc.comp (continuous_pi fun i => he.comp (continuous_apply i)), ?_⟩
    funext g
    have := dn_comp_monoidHom e.toMonoidHom ρ ρ' h 2 c g
    rw [hcf] at this
    refine this.trans ?_
    exact congrArg f (funext fun i => e.symm_apply_apply _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenvectorEqZeroOfMemTwistedSpanChain
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem map_mem_aug_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (A B : Set G) (z : G) (h : ∀ y ∈ B, z * y * z⁻¹ ∈ A) (u : V) (hu : u ∈ aug π B (fun _ => 1)) :
    π z u ∈ aug π A (fun _ => 1) := by
  have hle : aug π B (fun _ => 1) ≤ (aug π A (fun _ => 1)).comap (π z) := by
    unfold aug
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, w, rfl⟩
    refine Submodule.subset_span ⟨z * y * z⁻¹, h y hy, π z w, ?_⟩
    have e : π (z * y * z⁻¹) (π z w) = π z (π y w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [e, map_sub, map_smul]
  exact hle hu

theorem aug_mono_set {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    {A B : Set G} (θ : G → ℂ) (h : A ⊆ B) : aug π A θ ≤ aug π B θ := by
  unfold aug
  refine Submodule.span_mono ?_
  rintro x ⟨y, hy, w, rfl⟩
  exact ⟨y, h hy, w, rfl⟩

theorem eig_eq_zero_of_mem_aug_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ z hJ hN hmono h0 hconj h1 hz m
  induction m with
  | zero =>
    intro u hu heig
    refine (_root_.GlobalTheory.PsType.eig_compl_aug G V π hπ (N 0) (fun _ => 1) (hN 0)).1 u hu ?_
    intro y hy
    rw [heig y (h0 y hy).1, (h0 y hy).2]
  | succ m ih =>
    intro u hu heig
    obtain ⟨u', hu'eig, hsub⟩ := (_root_.GlobalTheory.PsType.eig_compl_aug G V π hπ (N 1) (fun _ => 1) (hN 1)).2 u
    have hsub' : u - u' ∈ aug π (N (m + 1)) (fun _ => 1) :=
      aug_mono_set π _ (hmono (Nat.succ_le_succ (Nat.zero_le m))) hsub
    have hu' : u' ∈ aug π (N (m + 1)) (fun _ => 1) := by
      have := Submodule.sub_mem _ hu hsub'
      simpa using this
    have hzu : π z u' ∈ aug π (N m) (fun _ => 1) :=
      map_mem_aug_of_conj π (N m) (N (m + 1)) z (fun y hy => (hconj m y).1 hy) u' hu'
    have hzeig : IsEig π J θ (π z u') :=
      _root_.GlobalTheory.PsType.isEig_translate_of_sub_mem_aug G V π hπ J (N 0) (N 1) θ z hJ (hN 0) h0 (hconj 0) hz u u' heig hu'eig hsub
    have hz0 : π z u' = 0 := ih _ hzu hzeig
    have hu0 : u' = 0 := by
      have e : π z⁻¹ (π z u') = u' := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [← e, hz0, map_zero]
    rw [hu0, sub_zero] at hsub
    exact _root_.GlobalTheory.PsType.eig_eq_zero_of_mem_aug_of_not_intertwine G V π hπ J (N 1) θ hJ (hN 1) h1 u hsub heig

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvInj

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def zpHom (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpHom p Ω z := by
  simp [zp, zpHom, HahnSeries.C_apply]

theorem psi_C {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (z : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
  have hpn : ((p : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [h.sub (HahnSeries.C z) (HahnSeries.C z), zp, HahnSeries.C_apply]
  · intro i
    by_cases hi : i = 0
    · simp [hi, HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero hpn hi
      simp [hi, this, HahnSeries.C_apply, HahnSeries.coeff_single]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [this, HahnSeries.C_apply, HahnSeries.coeff_single]

theorem psi_int {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (y : O0 p) :
    IsInt (p := p) (ψ y) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_
    rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap
  have hm : ψ y ∈ ψ.range := ⟨y, rfl⟩
  rw [h.rng, Subalgebra.mem_toSubring] at hm
  exact adjoin_le_integralClosure hq hm

theorem dvd_C_iff (k : ℕ) (z : ℤ_[p]) : (p : Lau p) ^ k ∣ HahnSeries.C z ↔ (p : ℤ_[p]) ^ k ∣ z := by
  rw [GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
  constructor
  · intro h; simpa [HahnSeries.C_apply, HahnSeries.coeff_single] using h 0
  · intro h m
    by_cases hm : m = 0
    · simpa [hm, HahnSeries.C_apply, HahnSeries.coeff_single] using h
    · simp [hm, HahnSeries.C_apply, HahnSeries.coeff_single]

section Val

variable (v : Valuation Ω ℝ≥0)

theorem cong_iff (hv : ∀ x, v x ≤ 1 ↔ IsInt (p := p) x) (hp0 : 0 < v (p : Ω)) (k : ℕ) (y : Ω) :
    Cong (p := p) k y 0 ↔ v y ≤ v (p : Ω) ^ k := by
  have hpk : (p : Ω) ^ k ≠ 0 := by
    intro h
    have := congrArg v h
    rw [map_pow, map_zero] at this
    exact (pow_pos hp0 k).ne' this
  constructor
  · rintro ⟨z, hz, e⟩
    rw [sub_zero] at e
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le' ((hv z).2 hz)
  · intro hy
    refine ⟨y / (p : Ω) ^ k, (hv _).1 ?_, by rw [sub_zero]; field_simp⟩
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hy zero_le'

def S (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (b : Fin F → Fin E → Lau p) : Ω :=
  ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))

theorem S_mul (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (m : ℕ) (b : Fin F → Fin E → Lau p) :
    S ψ π κ (fun j s => (p : Lau p) ^ m * b j s) = (p : Ω) ^ m * S ψ π κ b := by
  simp only [S, map_mul, map_pow, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

theorem S_le_one (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1)
    (hψ : ∀ y, v (ψ y) ≤ 1) (b : Fin F → Fin E → Lau p) : v (S ψ π κ b) ≤ 1 := by
  refine v.map_sum_le fun j _ => v.map_sum_le fun s _ => ?_
  rw [map_mul, map_mul, map_pow]
  exact mul_le_one' (mul_le_one' (hκ j) (pow_le_one' hπ _)) (hψ _)

theorem key_k (hp0 : 0 < v (p : Ω)) (hp1 : v (p : Ω) < 1) (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω)
    (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1) (hψ : ∀ y, v (ψ y) ≤ 1)
    (K1 : ∀ b : Fin F → Fin E → Lau p, v (S ψ π κ b) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s) :
    ∀ (k : ℕ) (b : Fin F → Fin E → Lau p), v (S ψ π κ b) ≤ v (p : Ω) ^ k ↔ ∀ j s, (p : Lau p) ^ k ∣ b j s := by
  intro k
  induction k with
  | zero => intro b; simpa using S_le_one v ψ π κ hπ hκ hψ b
  | succ k ih =>
    intro b
    constructor
    · intro h
      have h1 : ∀ j s, (p : Lau p) ∣ b j s :=
        K1 b (h.trans (pow_le_of_le_one zero_le' hp1.le (Nat.succ_ne_zero k)))
      choose b' hb' using h1
      have hb : b = fun j s => (p : Lau p) ^ 1 * b' j s := by
        funext j s; rw [pow_one]; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow, pow_one, pow_succ'] at h
      have h2 : v (S ψ π κ b') ≤ v (p : Ω) ^ k := le_of_mul_le_mul_left h hp0
      intro j s
      rw [hb' j s, pow_succ']
      exact mul_dvd_mul_left _ ((ih b').1 h2 j s)
    · intro h
      choose b' hb' using h
      have hb : b = fun j s => (p : Lau p) ^ (k + 1) * b' j s := by
        funext j s; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le' (S_le_one v ψ π κ hπ hκ hψ b')

end Val

end GlobalTheory.Glue.EvInj

end


open GlobalTheory.Glue.EvInj in
theorem GlobalTheory.Glue.ev_cong_iff_and_unit :
    ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' →
        (Cong (p := p) k x 0 ↔ ∀ r, Cong (p := p) k (c r) 0) ∧
          ((∃ r, c r ≠ 0 ∧ IsInt (p := p) (c r)⁻¹) → x ≠ 0 ∧ IsInt (p := p) x⁻¹) := by
  intro p _ Ω _ _ hC T n ψ hψ k c x x' hEv
  have hval : ∃ v : Valuation Ω ℝ≥0, (∀ y, v y ≤ 1 ↔ IsInt (p := p) y) ∧
      0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
    obtain ⟨_, _, hirr⟩ := _root_.GlobalTheory.K5.completed_laurent_isDVR p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hirr.maximalIdeal_eq]
      exact _root_.GlobalTheory.K5.o0_isAdicComplete_span_p p
    have := hC.alg
    obtain ⟨v, hv⟩ :=
      _root_.GlobalTheory.valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω hC.inj
    have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine ⟨v, hv, (Valuation.pos_iff v).2 hp, ?_⟩
    have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
      simpa [IsInt] using GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ))
    refine lt_of_le_of_ne hle fun heq => ?_
    have hinv : v ((p : Ω)⁻¹) ≤ 1 := by rw [map_inv₀, heq, inv_one]
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ω)⁻¹, (hv _).1 hinv, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp]⟩
  obtain ⟨v, hv, hp0, hp1⟩ := hval
  obtain ⟨d, e, a, he, hc, hx, -⟩ := hEv
  have hψv : ∀ y, v (ψ y) ≤ 1 := fun y => (hv _).2 (psi_int hψ y)
  have hzp : ∀ z : ℤ_[p], v (zp Ω z) ≤ 1 := fun z => (hv _).2 (by rw [zp]; exact isIntegral_algebraMap)
  have hev : ∀ t, v (e t) ≤ 1 := fun t => (hv _).2 (he t).1
  have hcv : ∀ r, v (c r) ≤ 1 := fun r => by
    rw [hc r]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hzp _)
  have hxv : v x ≤ 1 := by
    rw [hx]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hψv _)
  refine ⟨?_, ?_⟩
  · obtain ⟨E, F, π, κ, lam, hE, -, hπE, hκ, hκu, hesp⟩ := GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements p Ω hC v hv hp0 hp1 d e he
    have hπ1 : v π < 1 := by
      by_contra h
      push_neg at h
      have h2 : 1 ≤ v π ^ E := one_le_pow₀ h
      rw [hπE] at h2
      exact absurd hp1 (not_lt.2 h2)
    have hκv : ∀ j, v (κ j) ≤ 1 := fun j => (hv _).2 (hκ j).1
    have LeviInductionForms : ∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 →
        ∀ j, (p : Lau p) ∣ b j := by
      intro b hb j
      have hr := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ F κ b (fun j => hκ j) hb
      rw [← pow_one (p : Lau p), GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
      intro r
      by_contra hnd
      have h1 := hκu (fun j => (b j).coeff r) ⟨j, by simpa using hnd⟩
      have h2 := hr r
      rw [h1] at h2
      exact lt_irrefl _ h2
    have K1 := _root_.GlobalTheory.KZ.ramified_divisible_of_unramified p Ω v ψ E F π κ hE hp0 hp1 hπE hκv hψv LeviInductionForms
    have Kk := key_k v hp0 hp1 ψ π κ hπ1.le hκv hψv K1
    obtain ⟨B, hB⟩ : ∃ B : Fin F → Fin E → Lau p, ∀ j s, B j s = ∑ t, HahnSeries.C (lam t j s) * a t :=
      ⟨_, fun _ _ => rfl⟩
    have hx2 : x = S ψ π κ B := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [S, hB, map_sum, map_mul, psi_C hψ, hx, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hc2 : ∀ r, c r = S ψ π κ (fun j s => HahnSeries.C ((B j s).coeff r)) := by
      intro r
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [S, psi_C hψ, hB, HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul, zp_eq, map_sum, map_mul, hc, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by
        rw [← HahnSeries.C_mul_eq_smul, map_mul, map_mul, psi_C hψ, psi_C hψ, zp_eq, zp_eq]
        ring
    rw [cong_iff v hv hp0, hx2, Kk]
    simp_rw [cong_iff v hv hp0, hc2, Kk, dvd_C_iff, GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
    exact ⟨fun h r j s => h j s r, fun h j s r => h r j s⟩
  · rintro ⟨r, hr0, hri⟩
    have hcr : v (c r) = 1 := by
      refine le_antisymm (hcv r) ?_
      have h1 := (hv _).2 hri
      rw [map_inv₀] at h1
      have h0 : v (c r) ≠ 0 := (Valuation.ne_zero_iff v).2 hr0
      exact (inv_le_one₀ (pos_iff_ne_zero.2 h0)).1 h1
    have hx1 : v x = 1 := by
      refine le_antisymm hxv (not_lt.1 fun hlt => ?_)
      have h3 := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ d e a he (by rwa [← hx]) r
      rw [← hc r, hcr] at h3
      exact lt_irrefl _ h3
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx1
      exact zero_ne_one hx1
    exact ⟨hx0, (hv _).1 (by rw [map_inv₀, hx1, inv_one])⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoboundaryOfSubsingletonContCohomologyThre
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem exists_coboundary_of_subsingleton_Hn_three :
    ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  intro R _ Γ _ _ M _ _ _ _ ρ hs c hc hcoc
  let f : (Fin 3 → Γ) → M := fun x => c (x 0, x 1, x 2)
  have hf : Continuous f := hc.comp (by fun_prop)
  have hd : dn ρ 3 f = 0 := by
    funext g
    rw [dn_apply, Fin.sum_univ_four]
    have e := hcoc (g 0) (g 1) (g 2) (g 3)
    have e0 : (f fun i => g i.succ) = c (g 1, g 2, g 3) := rfl
    have e1 : f (Fin.contractNth 0 (· * ·) g) = c (g 0 * g 1, g 2, g 3) := rfl
    have e2 : f (Fin.contractNth 1 (· * ·) g) = c (g 0, g 1 * g 2, g 3) := rfl
    have e3 : f (Fin.contractNth 2 (· * ·) g) = c (g 0, g 1, g 2 * g 3) := rfl
    have e4 : f (Fin.contractNth 3 (· * ·) g) = c (g 0, g 1, g 2) := rfl
    rw [e0, e1, e2, e3, e4, Pi.zero_apply, ← e]
    norm_num [pow_succ]
    abel
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at hs
  obtain ⟨w, hw, hwf⟩ : ∃ w : (Fin 2 → Γ) → M, Continuous w ∧ dn ρ 2 w = f :=
    hs (x := ⟨f, hf, hd⟩) trivial
  refine ⟨fun p => w ![p.1, p.2], hw.comp (by fun_prop), fun g h k => ?_⟩
  have e := congrFun hwf ![g, h, k]
  rw [dn_apply, Fin.sum_univ_three] at e
  have e0 : (fun i : Fin 2 => (![g, h, k] : Fin 3 → Γ) i.succ) = ![h, k] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g * h, k] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h * k] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h] := by
    funext i; fin_cases i <;> rfl
  have e4 : f ![g, h, k] = c (g, h, k) := rfl
  rw [e0, e1, e2, e3, e4] at e
  rw [← e]
  norm_num [pow_succ]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUnStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRoot_of_mem_Un_of_jHol : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  first | exact @GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | exact GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un | (intros; apply GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un <;> assumption)
end

