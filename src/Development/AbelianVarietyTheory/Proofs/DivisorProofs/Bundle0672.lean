module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.EtLevMorita

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

section Act

variable {O : Type} [Ring O] {G : Type} [CommGroup G] (act : O → G → G)
  (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
  (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)

include hmul in
theorem act_one_eq (b : O) : act b 1 = 1 := by
  have h := hmul b 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.1 h

include hadd in
theorem act_zero_eq (g : G) : act 0 g = 1 := by
  have h := hadd 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.1 h

def actModule : Module O (Additive G) where
  smul b x := Additive.ofMul (act b x.toMul)
  one_smul x := by show Additive.ofMul (act 1 x.toMul) = x; rw [hone]; rfl
  mul_smul b c x := congrArg Additive.ofMul (hcomp b c x.toMul)
  smul_zero b := congrArg Additive.ofMul (act_one_eq act hmul b)
  smul_add b x y := congrArg Additive.ofMul (hmul b x.toMul y.toMul)
  add_smul b c x := congrArg Additive.ofMul (hadd b c x.toMul)
  zero_smul x := congrArg Additive.ofMul (act_zero_eq act hadd x.toMul)

end Act

end GlobalTheory.EtLevMorita


open GlobalTheory.EtLevMorita in
theorem GlobalTheory.EtLevMorita.exists_lev : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  intro p _ D w0 r hw hp G _ act hmul hone hcomp hadd f hfadd hfsm hfinj hfonto
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ => 1, fun _ _ => (_root_.mul_one 1).symm, fun b _ => (act_one_eq act hmul b).symm,
      fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
    · simp only [true_iff]
      have hx : x = algebraMap (𝓞 D.F) D.O 1 • x := by simp
      rw [hx]
      exact Submodule.subset_span ⟨1, by simp, x, rfl⟩
    · have h1 := hg 1 (by simp)
      rw [map_one, hone] at h1
      exact h1.symm
  · haveI := isLocalRing_quot_pow w0 r hr.ne'
    letI : Module D.O (Additive G) := actModule act hmul hone hcomp hadd
    letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    have hsm : ∀ (b : D.O) (x : Additive G), b • x = Additive.ofMul (act b x.toMul) := fun _ _ => rfl
    let T : Submodule D.O (Additive G) :=
      { carrier := {x | ∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) x.toMul = 1}
        add_mem' := fun {x y} hx hy c hc => by
          show act _ (x.toMul * y.toMul) = 1
          rw [hmul, hx c hc, hy c hc, _root_.mul_one]
        zero_mem' := fun c _ => act_one_eq act hmul _
        smul_mem' := fun b x hx c hc => by
          show act _ (act b x.toMul) = 1
          rw [← hcomp, Algebra.commutes, hcomp, hx c hc, act_one_eq act hmul] }
    have hf0 : f 0 = 1 := by
      have h := hfadd 0 0
      rw [add_zero] at h
      exact left_eq_mul.1 h
    have hfT : ∀ a, Additive.ofMul (f a) ∈ T := fun a c hc => by
      show act _ (f a) = 1
      rw [← hfsm, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_smul, hf0]
    let fl : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) →ₗ[𝓞 D.F] T :=
      { toFun := fun a => ⟨Additive.ofMul (f a), hfT a⟩
        map_add' := fun a a' => Subtype.ext (by
          show Additive.ofMul (f (a + a')) = Additive.ofMul (f a) + Additive.ofMul (f a')
          rw [hfadd]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          show Additive.ofMul (f (c • a)) = algebraMap (𝓞 D.F) D.O c • Additive.ofMul (f a)
          rw [← algebraMap_smul (𝓞 D.F ⧸ w0 ^ r) c a, Ideal.Quotient.algebraMap_eq, hfsm]
          rfl) }
    have hfl : Function.Bijective fl := by
      refine ⟨fun a a' h => hfinj (congrArg (fun t : T => (t : Additive G).toMul) h), fun t => ?_⟩
      obtain ⟨a, ha⟩ := hfonto (t : Additive G).toMul t.2
      exact ⟨a, Subtype.ext (by show Additive.ofMul (f a) = _; rw [ha]; rfl)⟩
    let eT : T ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) := (LinearEquiv.ofBijective fl hfl).symm
    obtain ⟨g, hgs, hgsm, hgker⟩ := GlobalTheory.T.level_quotient_module_surjection p D w0 r hw
    let gl : D.La →ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c x => by
          show g (algebraMap (𝓞 D.F) D.O c • x) = c • g x
          rw [hgsm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
    have hker : LinearMap.ker gl = (wSub D w0 r).restrictScalars (𝓞 D.F) := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact hgker x
    let eL : (D.La ⧸ wSub D w0 r) ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      (Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D w0 r)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ gl.quotKerEquivOfSurjective hgs
    obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power p D w0 r hw hp
    obtain ⟨e⟩ := GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix (𝓞 D.F) (w0 ^ r) inferInstance D.m D.n D.m_pos D.O φ hφs hφk
      (D.La ⧸ wSub D w0 r) T eL eT
    refine ⟨fun x => ((e (Submodule.Quotient.mk x) : T) : Additive G).toMul, fun x y => ?_, fun b x => ?_,
      fun x => ?_, fun g hg => ?_⟩
    · simp only [Submodule.Quotient.mk_add, map_add (f := _), Submodule.coe_add, toMul_add]
    · simp only [Submodule.Quotient.mk_smul, map_smul, Submodule.coe_smul, hsm, toMul_ofMul]
    · rw [toMul_eq_one, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm ⟨Additive.ofMul g, hg⟩)
      refine ⟨y, ?_⟩
      simp only [hy, LinearEquiv.apply_symm_apply, toMul_ofMul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupFormalChartOfConnected
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartEx

theorem isEval_comp {p : ℕ} {O A A' σ : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A]
    [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] A')
    (h : IsEval p x E) : IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨a, ha⟩ := hN f hf
  exact ⟨φ a, by rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]⟩

theorem nil_map {p : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {a : A}
    (h : ∃ N : ℕ, (p : A) ∣ a ^ N) : ∃ N : ℕ, (p : A') ∣ φ a ^ N := by
  obtain ⟨N, b, hb⟩ := h
  exact ⟨N, φ b, by rw [← map_pow, hb, map_mul, map_natCast]⟩

theorem eq_zero_of_dvd {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {c : O} (h : ∀ m : ℕ, (p : O) ^ m ∣ c) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun m => ?_
  obtain ⟨b, hb⟩ := h m
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, hb⟩

theorem eq_zero_of_ker {p : ℕ} {O σ : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {A : ℕ → Type} [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)]
    (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hker : ∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f)
    {f : MvPowerSeries σ O} (hf : ∀ n, E n f = 0) : f = 0 := by
  ext α
  rw [map_zero]
  refine eq_zero_of_dvd (p := p) fun m => ?_
  obtain ⟨n, hn⟩ := hker m (α.degree + 1)
  exact hn f (hf n) α (Nat.lt_succ_self _)

theorem chart_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, ev, hnil, hev, hres, haug, hsurj, hker⟩ := GlobalTheory.T.exists_coordinates_of_isConnected p C v O hv G hG
  have hc2 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    fun n => _root_.GlobalTheory.FinProjComplete.isAdicComplete_span_natCast p O _
  have hc3 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] (G.A n ⊗[O] G.A n))})
      (G.A n ⊗[O] (G.A n ⊗[O] G.A n)) := fun n => _root_.GlobalTheory.FinProjComplete.isAdicComplete_span_natCast p O _
  have hcA : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := fun n => _root_.GlobalTheory.FinProjComplete.isAdicComplete_span_natCast p O _
  have nil2 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) j ^ N := by
    rintro n (i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
    · simpa using nil_map (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
  have nil3 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] (G.A n ⊗[O] G.A n)) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) j ^ N := by
    rintro n (i | i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
  have hE2 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n,
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) E := by
    intro n
    haveI := hc2 n
    exact (_root_.GlobalTheory.CEval.continuous_eval p O _ _ _ (nil2 n)).1.exists
  choose E₂ hE₂ using hE2
  have hE3 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n),
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) E := by
    intro n
    haveI := hc3 n
    exact (_root_.GlobalTheory.CEval.continuous_eval p O _ _ _ (nil3 n)).1.exists
  choose E₃ hE₃ using hE3
  have hsurj2 : ∀ n, Function.Surjective (E₂ n) := fun n => by
    haveI := hc2 n
    exact _root_.GlobalTheory.SurjTens.surjective_eval_tmul p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n)
  have hker2 : ∀ m N : ℕ, ∃ n, ∀ f, E₂ n f = 0 → ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    exact ⟨n, _root_.GlobalTheory.KerTensor.ker_tensor p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn⟩
  have hker3 : ∀ m N : ℕ, ∃ n, ∀ f, E₃ n f = 0 → ∀ α : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    have hn2 := _root_.GlobalTheory.KerTensor.ker_tensor p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn
    have hpt : (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) fun j => (1 : G.A n) ⊗ₜ[O] (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] x n i) j)) = (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) := by
      funext j
      rcases j with j | j | j <;> rfl
    have hE3' := hE₃ n
    rw [← hpt] at hE3'
    exact ⟨n, _root_.GlobalTheory.KerTensor.ker_tensor p O _ _ _ _ (x n) _ (ev n) (E₂ n) (E₃ n) m N (hev n) (hE₂ n) hE3' (hsurj n) (hsurj2 n) hn hn2⟩
  have hstep : ∀ i n f, E₂ (n + 1) f = Coalgebra.comul (R := O) (x (n + 1) i) →
      E₂ n f = Coalgebra.comul (R := O) (x n i) := by
    intro i n f hf
    let ρ : G.A (n + 1) ⊗[O] G.A (n + 1) →ₐ[O] G.A n ⊗[O] G.A n :=
      Algebra.TensorProduct.map (AlgHomClass.toAlgHom (G.res n)) (AlgHomClass.toAlgHom (G.res n))
    have hρ : ρ.comp (E₂ (n + 1)) = E₂ n := by
      haveI := hc2 n
      refine (_root_.GlobalTheory.CEval.continuous_eval p O _ _ _ (nil2 n)).1.unique ?_ (hE₂ n)
      have h1 := isEval_comp ρ (hE₂ (n + 1))
      convert h1 using 1
      funext j
      rcases j with j | j <;> simp [ρ, AlgHomClass.toAlgHom, hres]
    rw [← hρ, AlgHom.comp_apply, hf]
    exact (CoalgHomClass.map_comp_comul_apply (G.res n) (x (n + 1) i)).trans (by rw [hres])
  have hμ : ∀ i, ∃ g, ∀ n, E₂ n g = Coalgebra.comul (R := O) (x n i) := by
    intro i
    exact _root_.GlobalTheory.CChartLimit.exists_series_of_compatible p O (Fin d ⊕ Fin d) (fun n => G.A n ⊗[O] G.A n) (fun n => (hc2 n).toIsHausdorff) _ E₂
      (fun n => Coalgebra.comul (R := O) (x n i)) hE₂ (fun n => hsurj2 n _) (hstep i) hker2
  choose μ hμ using hμ
  have hconst : ∀ i, constantCoeff (μ i) = 0 :=
    GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' p O (G.A 0) (x 0) (E₂ 0) μ (haug 0) (hE₂ 0) (fun i => hμ i 0)
  refine ⟨d, ⟨⟨x, ev, E₂, μ, hnil, hev, hE₂, hres, haug, hsurj, hker, ?_, fun n i => hμ i n⟩⟩⟩
  refine ⟨hconst, ?_, fun i => ?_, ?_⟩
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) ev hker fun n => ?_)
    haveI := hcA n
    rw [map_sub, GlobalTheory.T.formalChart_groupLaw_eval_right_unit p O (G.A n) (x n) (ev n) (E₂ n) μ (hnil n) (haug n) (hev n) (hE₂ n) (fun i => hμ i n) i,
      (hev n).1 i, sub_self]
  · refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₂ hker2 fun n => ?_)
    haveI := hc2 n
    rw [map_sub, GlobalTheory.T.eval_swap_eq' p O (G.A n) (x n) (E₂ n) μ (hnil n) (hE₂ n) (fun i => hμ i n) i, sub_self]
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₃ hker3 fun n => ?_)
    haveI := hc3 n
    rw [map_sub, GlobalTheory.T.isEval_comul_assoc_of_isEval p O (G.A n) (x n) (E₂ n) (E₃ n) μ (hnil n) hconst (hE₂ n) (hE₃ n) (fun i => hμ i n) i, sub_self]

end GlobalTheory.ChartEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartPair

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem exists_affine_pt (y : Sp ℂ ⟶ X) : ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ y ⁻¹ᵁ U := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ ↦ ?_⟩
  have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  subst this
  exact hy

theorem isOpen_dom (u : Unif F s σ) (U : X.Opens) : IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
  (u.hol U 0).1

def Good (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  (∀ p ∈ W, p.1 ∈ F.V) ∧ ∃ U : X.Opens, IsAffineOpen U ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U

def charts (u : Unif F s σ) : Charts F where
  K := {W : Opens (Tot I g) // Good u W}
  W k := k.1
  base k := k.2.1
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans {l m k k' k''} h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

end GlobalTheory.AnPer.ChartPair

namespace GlobalTheory.AnPer.ChartPair

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}
  {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V}

def pairCharts (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂) : Charts F₁ where
  K := {q : Opens (Tot I₁ g₁) × Opens (Tot I₂ g₂) //
    Good u₁ q.1 ∧ Good u₂ q.2 ∧ ∀ p ∈ q.1, ((b p.1, M p.2) : Tot I₂ g₂) ∈ q.2}
  W k := k.1.1
  base k := k.2.1.1
  le l k' k := (∀ p ∈ k'.1.1, F₁.shift l p ∈ k.1.1) ∧ ∀ p ∈ k'.1.2, F₂.shift (A l) p ∈ k.1.2
  le_refl k := ⟨fun p hp ↦ by rwa [F₁.shift_zero], fun p hp ↦ by rwa [map_zero, F₂.shift_zero]⟩
  le_trans {l m k k' k''} h h' := ⟨fun p hp ↦ by rw [F₁.shift_add]; exact h.1 _ (h'.1 p hp),
    fun p hp ↦ by rw [map_add (f := _), F₂.shift_add]; exact h.2 _ (h'.2 p hp)⟩
  maps h := h.1

theorem exists_pair (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ)
    (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) :
    ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧
      (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧
      (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧
      ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  let Φ : Tot I₁ g₁ → Tot I₂ g₂ := fun p ↦ (b p.1, M p.2)
  have hΦ : ∀ l (p : Tot I₁ g₁), p.1 ∈ F₁.V → Φ (F₁.shift l p) = F₂.shift (A l) (Φ p) := by
    intro l p hp
    simp only [Φ, Fam.shift, map_add (f := _), hτ l p.1 hp]
  have hcont : ContinuousOn Φ {p : Tot I₁ g₁ | p.1 ∈ F₁.V} :=
    (hb.continuousOn.comp continuous_fst.continuousOn fun p hp ↦ hp).prodMk
      (M.continuous_of_finiteDimensional.comp continuous_snd).continuousOn
  refine ⟨pairCharts u₁ u₂ b M A, charts u₂, fun k ↦ ⟨k.1.2, k.2.2.1⟩, ⟨?_, ?_⟩,
    fun k ↦ k.2.1.2, fun k ↦ k.2.2, fun k ↦ k.2.2.2, fun l k' k h ↦ h.2⟩
  · intro p hp
    obtain ⟨U₁, hU₁, h₁⟩ := exists_affine_pt (u₁.E p)
    obtain ⟨U₂, hU₂, h₂⟩ := exists_affine_pt (u₂.E (Φ p))
    let O₁ := {q : Tot I₁ g₁ | q.1 ∈ F₁.V ∧ ⊤ ≤ u₁.E q ⁻¹ᵁ U₁}
    let O₂ := {q : Tot I₂ g₂ | q.1 ∈ F₂.V ∧ ⊤ ≤ u₂.E q ⁻¹ᵁ U₂}
    have hO₂ : IsOpen O₂ := isOpen_dom u₂ U₂
    have hO₁ : IsOpen (O₁ ∩ Φ ⁻¹' O₂) :=
      (hcont.mono fun (q : Tot I₁ g₁) (hq : q ∈ O₁) ↦ hq.1).isOpen_inter_preimage (isOpen_dom u₁ U₁) hO₂
    refine ⟨⟨(⟨O₁ ∩ Φ ⁻¹' O₂, hO₁⟩, ⟨O₂, hO₂⟩),
      ⟨fun q hq ↦ hq.1.1, U₁, hU₁, fun q hq ↦ hq.1.2⟩, ⟨fun q hq ↦ hq.1, U₂, hU₂, fun q hq ↦ hq.2⟩,
      fun q hq ↦ hq.2⟩, ?_⟩
    exact ⟨⟨hp, h₁⟩, hbV _ hp, h₂⟩
  · intro l k₁ k₂ p hp hp'
    have hb₁ := k₁.2.1.1
    have hb₂ := k₁.2.2.1.1
    have o₁ : IsOpen ((k₁.1.1 : Set (Tot I₁ g₁)) ∩ F₁.shift l ⁻¹' k₂.1.1) :=
      (F₁.shift_analytic l hb₁).continuousOn.isOpen_inter_preimage k₁.1.1.isOpen k₂.1.1.isOpen
    have o₂ : IsOpen ((k₁.1.2 : Set (Tot I₂ g₂)) ∩ F₂.shift (A l) ⁻¹' k₂.1.2) :=
      (F₂.shift_analytic (A l) hb₂).continuousOn.isOpen_inter_preimage k₁.1.2.isOpen k₂.1.2.isOpen
    obtain ⟨U₁, hU₁, h₁⟩ := k₁.2.1.2
    obtain ⟨U₂, hU₂, h₂⟩ := k₁.2.2.1.2
    refine ⟨⟨(⟨_, o₁⟩, ⟨_, o₂⟩), ⟨fun q hq ↦ hb₁ q hq.1, U₁, hU₁, fun q hq ↦ h₁ q hq.1⟩,
      ⟨fun q hq ↦ hb₂ q hq.1, U₂, hU₂, fun q hq ↦ h₂ q hq.1⟩, fun q hq ↦ ⟨k₁.2.2.2 q hq.1, ?_⟩⟩,
      ⟨hp, hp'⟩, ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩, ⟨fun q hq ↦ hq.2, fun q hq ↦ hq.2⟩⟩
    · show F₂.shift (A l) (Φ q) ∈ k₂.1.2
      rw [← hΦ l q (hb₁ q hq.1)]
      exact k₂.2.2.2 _ hq.2
    · rw [F₁.shift_zero]; exact hq.1
    · rw [map_zero, F₂.shift_zero]; exact hq.1

end GlobalTheory.AnPer.ChartPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroMove

theorem gen_hom {A C : Type} [CommRing A] [CommRing C] {g : ℕ} (ψ : A →+* C) (D : Fin g → A →+ A)
    (h1 : ∀ a, D a 1 = 0) (hL : ∀ a x y, D a (x * y) = x * D a y + y * D a x)
    (n : Fin g → C) (hn : ∀ a b, n a * n b = 0) :
    ∃ ψ' : A →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (D a x) * n a := by
  have hsq : ∀ (u v : Fin g → C), (∑ a, u a * n a) * (∑ b, v b * n b) = 0 := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    calc u a * n a * (v b * n b) = u a * v b * (n a * n b) := by ring
      _ = 0 := by rw [hn a b, mul_zero]
  refine ⟨{ toFun := fun x => ψ x + ∑ a, ψ (D a x) * n a,
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun x => rfl⟩
  · simp [h1]
  · intro x y
    have e := hsq (fun a => ψ (D a x)) (fun a => ψ (D a y))
    simp only [hL, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib]
    have ex : ∑ a, ψ x * ψ (D a y) * n a = ψ x * ∑ a, ψ (D a y) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have ey : ∑ a, ψ y * ψ (D a x) * n a = ψ y * ∑ a, ψ (D a x) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [ex, ey]
    linear_combination (-1 : C) * e
  · simp
  · intro x y
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
    ring

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : R ⊗[ℂ] S) :
    LinearMap.lTensor R d.toLinearMap (x * y) =
      x * LinearMap.lTensor R d.toLinearMap y + y * LinearMap.lTensor R d.toLinearMap x := by
  first
  | exact @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | (apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz ..)

theorem lTensor_one {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) : LinearMap.lTensor R d.toLinearMap (1 : R ⊗[ℂ] S) = 0 := by
  rw [Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem sqZeroMove : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  exact gen_hom ψ (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => lTensor_one _) (fun a x y => lTensor_leibniz _ x y) n hn

end GlobalTheory.SqZeroMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloEtaleIffCharts
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.holo_etale_iff_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ u : Y → ℂ, (Holo n (fun y : U => z y) (fun y : U => u y) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) := by
  intro n Y _ _ _ _ _ ι La _ A U z hz u
  have h := _root_.GlobalTheory.OTY.holo_etale_iff_holo_chart n Y ι La A U z hz Set.univ u isOpen_univ
  simp only [Set.preimage_univ, Set.inter_univ] at h
  exact h
end

