module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.PointSumConj

theorem exists_conj_iff {G : Type} [Group G] (K : Subgroup G) (a m : G) :
    (∃ k ∈ K, a * k * a⁻¹ = m) ↔ a⁻¹ * m * a ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : a⁻¹ * (a * k * a⁻¹) * a = k := by group
    rw [this]; exact hk
  · intro h
    exact ⟨a⁻¹ * m * a, h, by group⟩

theorem mem_stab {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) (z : Γ) :
    z ∈ stab ι₁ ι₂ K₁ K₂ x ↔ x.1⁻¹ * ι₁ z * x.1 ∈ K₁ ∧ x.2⁻¹ * ι₂ z * x.2 ∈ K₂ := by
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, exists_conj_iff]

theorem finsum_dc_translate {G : Type} [Group G] (H H' K : Subgroup G) (a : G)
    (hH : ∀ h ∈ H, a * h * a⁻¹ ∈ H') (hH' : ∀ h ∈ H', a⁻¹ * h * a ∈ H) (F F' : G → ℂ)
    (hF : ∀ h ∈ H, ∀ k ∈ K, ∀ x, F (h * x * k) = F x) (hF' : ∀ x, F' (a * x) = F x) :
    ∑ᶠ q : DoubleCoset.Quotient (H' : Set G) (K : Set G), F' (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G), F (Quotient.out q) := by
  have key : ∀ x, F' (Quotient.out (DoubleCoset.mk H' K (a * x))) = F x := by
    intro x
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H' K (a * x))).symm
    rw [he]
    have : h' * (a * x) * k = a * ((a⁻¹ * h' * a) * x * k) := by group
    rw [this, hF', hF _ (hH' _ hh') _ hk]
  refine (finsum_eq_of_bijective (fun q : DoubleCoset.Quotient (H : Set G) (K : Set G) =>
    DoubleCoset.mk H' K (a * Quotient.out q)) ⟨?_, ?_⟩ (fun q => (key _).symm)).symm
  · intro q₁ q₂ h
    obtain ⟨h', hh', k, hk, he⟩ := (@DoubleCoset.eq _ _ H' K _ _).1 h
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
    refine (@DoubleCoset.eq _ _ H K _ _).2 ⟨a⁻¹ * h' * a, hH' _ hh', k, hk, ?_⟩
    have : Quotient.out q₂ = a⁻¹ * (a * Quotient.out q₂) := by group
    rw [this, he]; group
  · intro q'
    refine ⟨DoubleCoset.mk H K (a⁻¹ * Quotient.out q'), ?_⟩
    obtain ⟨h, hh, k, hk, he⟩ := (@DoubleCoset.eq _ _ H K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk H K (a⁻¹ * Quotient.out q'))).symm
    simp only
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' q']
    exact (@DoubleCoset.eq _ _ H' K _ _).2 ⟨(a * h * a⁻¹)⁻¹, H'.inv_mem (hH _ hh), k⁻¹, K.inv_mem hk, by group⟩

end GlobalTheory.PointSumConj

namespace GlobalTheory.PointSumConj

theorem conj_mem_iff {G : Type} [Group G] (K : Subgroup G) {k : G} (hk : k ∈ K) (m : G) :
    k⁻¹ * m * k ∈ K ↔ m ∈ K := by
  rw [Subgroup.mul_mem_cancel_right K hk, Subgroup.mul_mem_cancel_left K (K.inv_mem hk)]

theorem card_stab_translate {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (y : Γ) (x k : G₁ × G₂) (hk : k ∈ K₁.prod K₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ ((ι₁ y, ι₂ y) * x * k)) = Nat.card (stab ι₁ ι₂ K₁ K₂ x) := by
  rw [Subgroup.mem_prod] at hk
  refine (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj y).toEquiv fun z => ?_)).symm
  simp only [SetLike.mem_coe, mem_stab, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    Prod.fst_mul, Prod.snd_mul, map_mul, map_inv]
  have e1 : (ι₁ y * x.1 * k.1)⁻¹ * (ι₁ y * ι₁ z * (ι₁ y)⁻¹) * (ι₁ y * x.1 * k.1) =
      k.1⁻¹ * (x.1⁻¹ * ι₁ z * x.1) * k.1 := by group
  have e2 : (ι₂ y * x.2 * k.2)⁻¹ * (ι₂ y * ι₂ z * (ι₂ y)⁻¹) * (ι₂ y * x.2 * k.2) =
      k.2⁻¹ * (x.2⁻¹ * ι₂ z * x.2) * k.2 := by group
  rw [e1, e2, conj_mem_iff K₁ hk.1, conj_mem_iff K₂ hk.2]

theorem stab_conj {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (g₁ : G₁) (g₂ : G₂) (x : G₁ × G₂) :
    stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) K₁ K₂
      ((g₁⁻¹, g₂⁻¹) * x) = stab ι₁ ι₂ K₁ K₂ x := by
  ext z
  simp only [mem_stab, Prod.fst_mul, Prod.snd_mul, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e1 : (g₁⁻¹ * x.1)⁻¹ * (g₁⁻¹ * ι₁ z * g₁⁻¹⁻¹) * (g₁⁻¹ * x.1) = x.1⁻¹ * ι₁ z * x.1 := by group
  have e2 : (g₂⁻¹ * x.2)⁻¹ * (g₂⁻¹ * ι₂ z * g₂⁻¹⁻¹) * (g₂⁻¹ * x.2) = x.2⁻¹ * ι₂ z * x.2 := by group
  rw [e1, e2]

theorem pointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  intro Γ G₁ G₂ _ _ _ ι₁ ι₂ θ K₁ K₂ γ g₁ δ g₂ f φ hf hφ hγ hδ
  unfold pointSum
  refine finsum_dc_translate (ι₁.prod ι₂).range
    (((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁).prod ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)).range
    (K₁.prod K₂) (g₁⁻¹, g₂⁻¹) ?_ ?_
    (fun x => ((Nat.card (stab ι₁ ι₂ K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * θ x.2)))
    (fun x => ((Nat.card (stab ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂)
      K₁ K₂ x) : ℕ) : ℂ)⁻¹ * (f (x.1⁻¹ * (g₁⁻¹ * γ * g₁) * x.1) * φ (x.2⁻¹ * (g₂⁻¹ * δ * θ g₂) * θ x.2))) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply]
  · rintro _ ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext <;> simp [MulAut.conj_apply] <;> group
  · rintro _ ⟨y, rfl⟩ k hk x
    have hk' := (Subgroup.mem_prod).1 hk
    simp only [MonoidHom.prod_apply] at *
    rw [card_stab_translate ι₁ ι₂ K₁ K₂ y x k hk]
    congr 2
    · have e : ((ι₁ y, ι₂ y) * x * k).1⁻¹ * γ * ((ι₁ y, ι₂ y) * x * k).1 =
          k.1⁻¹ * (x.1⁻¹ * ((ι₁ y)⁻¹ * γ * ι₁ y) * x.1) * k.1 := by simp only [Prod.fst_mul]; group
      have e' : (ι₁ y)⁻¹ * γ * ι₁ y = γ := by rw [mul_assoc, ← hγ y]; group
      rw [e, e', hf _ hk'.1]
    · have e : ((ι₁ y, ι₂ y) * x * k).2⁻¹ * δ * θ ((ι₁ y, ι₂ y) * x * k).2 =
          k.2⁻¹ * (x.2⁻¹ * ((ι₂ y)⁻¹ * δ * θ (ι₂ y)) * θ x.2) * θ k.2 := by
        simp only [Prod.snd_mul, map_mul]; group
      have e' : (ι₂ y)⁻¹ * δ * θ (ι₂ y) = δ := by rw [mul_assoc, ← hδ y]; group
      rw [e, e', hφ _ hk'.2]
  · intro x
    rw [stab_conj]
    congr 2
    · congr 1; simp only [Prod.fst_mul]; group
    · congr 1; simp only [Prod.snd_mul, map_mul, map_inv]; group

end GlobalTheory.PointSumConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfSteps
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem limPt_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  intro hAdd hAct hCont
  intro C _ _ v d R _ _ O _ _ B hB σ _ κ _ w hw A a hA
  have hdI : ∀ c e e', IsIntV v (dAct C B c e e') := fun c e _ => hB.2.1 c e _
  have hAI : ∀ b e e', IsIntV v (A b e e') := by
    intro b e e'
    have h0 : IsIntV v (A b e e' - dAct C B (a 0 b) e e') := by
      have := hA 0 b e e'
      simpa [IsIntV] using this
    have : A b e e' = (A b e e' - dAct C B (a 0 b) e e') + dAct C B (a 0 b) e e' := by ring
    rw [this]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h0) ((ptIsIntV_iff _).1 (hdI _ _ _)))
  have hN : ∀ N, IntLog (fglOf hB) (∑ b, mv (dAct C B (a N b)) (w b)) := fun N =>
    Finset.sum_induction _ (IntLog (fglOf hB)) (fun x y hx hy => (hAdd C v d (fglOf hB) σ).2.2 x y hx hy)
      (hAdd C v d (fglOf hB) σ).1 (fun b _ => (hAct C v d R O B hB σ (a N b)).2 _ (hw b))
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have key : ∀ (M : κ → Matrix (Fin d) (Fin d) C) (i : Fin d),
      expPt (fglOf hB) (∑ b, mv (M b) (w b)) i =
        subst (fun q => ∑ x : κ × Fin d, M x.1 q x.2 • w x.1 x.2) (expOf (fglOf hB) i) := by
    intro M i
    unfold expPt
    congr 1
    funext q
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    rfl
  refine ⟨fun i => ?_, fun i α => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_apply, map_sum]
      exact Finset.sum_eq_zero fun b _ => cc_mv (A b) (hw0 b) i
  · obtain ⟨N₀, hN₀⟩ := hCont C v (Fin d) σ (κ × Fin d) (expOf (fglOf hB) i) (fun x => w x.1 x.2)
      (fun x => hw0 x.1 x.2) α
    have h1 := hN₀ (fun q x => A x.1 q x.2) (fun q x => dAct C B (a N₀ x.1) q x.2) (fun q x => hAI _ _ _)
      (fun q x => hdI _ _ _) (fun q x => hA N₀ x.1 q x.2)
    have h2 := (hN N₀).2 i α
    rw [key] at h2
    rw [key]
    rw [← sub_add_cancel (coeff α (subst (fun q => ∑ x : κ × Fin d, A x.1 q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))
      (coeff α (subst (fun q => ∑ x : κ × Fin d, dAct C B (a N₀ x.1) q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h1) ((ptIsIntV_iff _).1 h2))

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LimAct

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv
open ReciprocityTheory.ChartRestriction.G.TB (dAct)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA (dActH)

theorem exists_lim {O : Type} [CommRing O] (q : O) [IsAdicComplete (Ideal.span {q}) O] (g : ℕ → O)
    (hg : ∀ m n, m ≤ n → ∃ w, g n - g m = q ^ m * w) : ∃ L : O, ∀ n, ∃ w, L - g n = q ^ n * w := by
  have key : ∀ m n, m ≤ n → g m ≡ g n [SMOD (Ideal.span {q} ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    obtain ⟨w, hw⟩ := hg m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨-w, by rw [← neg_sub, hw]; ring⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {q}) g (fun {m n} h => key m n h)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, by rw [← neg_sub, ← ha]; ring⟩

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem isIntV_alg (o : X.O) : IsIntV (vX_vp X) (algebraMap X.O X.C o) := by
  rw [GlobalTheory.FactorDepth.isIntV_iff]; exact X.ints.map_le_one o

theorem le_v_pow_mul (N : ℕ) (o : X.O) :
    ((N : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * algebraMap X.O X.C o) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p, nsmul_one]
  have h := isIntV_alg X o
  unfold IsIntV at h
  calc ((N : ℝ) : WithTop ℝ) = (N : WithTop ℝ) := by norm_cast
    _ ≤ (N : WithTop ℝ) + vX_vp X (algebraMap X.O X.C o) := le_add_of_nonneg_right h

theorem eq_zero_of_le_v (x : X.C) (h : ∀ N : ℕ, ((N : ℝ) : WithTop ℝ) ≤ vX_vp X x) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ))
  have := h N
  rw [vX_vp_apply X hx, WithTop.coe_le_coe] at this
  linarith

end Val

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [inst : StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActXH : 𝓞 E →+* Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dActH X.C Ch.ch.B

theorem dActX_eq (a : 𝓞 E) : dActX Ch X a = dActXH Ch X a := rfl

def entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) : X.O :=
  X.ι (coeff (Finsupp.single ((0 : Fin 1), e') 1) (Ch.actT a e))

theorem alg_entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    algebraMap X.O X.C (entO Ch X a e e') = dActX Ch X a e e' := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  rw [entO, ← X.comp]
  show _ = coeff _ (Ch.ch.B.actK X.C a e)
  unfold FB.actK
  rw [Ch.gen.1.2.1 a e, coeff_map, coeff_map]
  rfl

theorem dActX_apply (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    dActX Ch X a e e' = X.ιF (letI := io.toAlgebra; dAct T.Fr Ch.ch.B a e e') := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  show coeff _ (Ch.ch.B.actK X.C a e) = X.ιF (coeff _ (Ch.ch.B.actK T.Fr a e))
  unfold FB.actK
  rw [coeff_map, coeff_map]
  rfl

theorem dActX_mulVec_lieVec (hst : ∀ a : 𝓞 E, star a = H.bar a) (φ : 𝓞 E →+* T.V) (τ : E →+* ℂ)
    (hφ : ∀ a : 𝓞 E, algebraMap T.V T.Fr (φ a) = io (embK c τ a)) (a : 𝓞 E) (i : Fin (Dw.mult τ)) :
    (dActX Ch X a).mulVec (lieVec Ch X ⟨τ, i⟩) = jX X (φ a) • lieVec Ch X ⟨τ, i⟩ := by
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  letI := io.toAlgebra
  have h := GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ⟨τ, i⟩
  funext e
  have h3 := congrArg X.ιF (congrFun h e)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h3 ⊢
  simp only [dActX_apply, lieVec, jX, RingHom.comp_apply, hφ, ← Ch.gen.1.2.2.2.2.2.2]
  exact h3

end Chart

theorem cauchy_eps_mul {R V : Type} [CommRing R] [CommRing V] (φ : R →+* V) (q : R) (ε x : ℕ → R) (t : V)
    (hε : ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M})
    (hx : ∀ N : ℕ, ∃ z, φ (x N) = t + φ q ^ N * z) (m n : ℕ) (hmn : m ≤ n) :
    ∃ w, ε n * x n - ε m * x m = q ^ m * w := by
  have hstep : ∀ N, ε (N + 1) * x (N + 1) - ε N * x N ∈ Ideal.span {q ^ N} := by
    intro N
    obtain ⟨z0, hz0⟩ := hx N
    obtain ⟨z1, hz1⟩ := hx (N + 1)
    obtain ⟨u0, hu0⟩ := (hε N).1
    obtain ⟨u1, hu1⟩ := (hε (N + 1)).1
    have ha : ε N * (x (N + 1) - x N) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨φ q * z1 - z0, by rw [map_sub, hz0, hz1]; ring⟩
    have hb : ε (N + 1) * (1 - ε N) ∈ Ideal.span {q ^ N} :=
      (hε (N + 1)).2 N (Nat.le_succ N) _ ⟨-u0, by rw [map_sub, map_one, hu0]; ring⟩
    have hc : ε N * (1 - ε (N + 1)) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨-(φ q * u1), by rw [map_sub, map_one, hu1]; ring⟩
    have e : ε (N + 1) * x (N + 1) - ε N * x N =
        ε N * (x (N + 1) - x N) + (ε (N + 1) * (1 - ε N) - ε N * (1 - ε (N + 1))) * x (N + 1) := by ring
    rw [e]
    exact Ideal.add_mem _ ha (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hb hc))
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨0, by ring⟩
  | succ n hmn ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨w + q ^ k * w', by linear_combination hw - hw'⟩

end GlobalTheory.IsoTriv.LimAct

namespace GlobalTheory.IsoTriv

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv.LimAct

theorem limActSt_of_epsSt (hε : EpsSt) : LimActSt := by
  intro E _ _ _ H Dw l Xo c inst hst T io y Ch p _ X τ
  obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c τ))
  have hP : φ (p : 𝓞 E) = (p : T.V) := map_natCast φ p
  have hp0 : φ (p : 𝓞 E) ≠ 0 := by rw [hP]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpu : ¬ IsUnit (φ (p : 𝓞 E)) := by rw [hP]; exact not_isUnit_p X
  obtain ⟨ε, hεN⟩ := hε (𝓞 E) T.V φ (p : 𝓞 E) hp0 hpu
  refine ⟨ε, fun t x hx => ?_⟩
  have hxN : ∀ N : ℕ, ∃ z, φ (x N) = t + φ (p : 𝓞 E) ^ N * z := fun N => by
    obtain ⟨z, hz⟩ := hx N
    exact ⟨z, by rw [hP]; exact IsFractionRing.injective T.V T.Fr ((hφ (x N)).trans hz)⟩
  have hcau := cauchy_eps_mul φ (p : 𝓞 E) ε x t hεN hxN
  have hent : ∀ e e', ∃ L : X.O, ∀ N, ∃ w, L - entO Ch X (ε N * x N) e e' = (p : X.O) ^ N * w := by
    intro e e'
    refine exists_lim (p : X.O) (fun N => entO Ch X (ε N * x N) e e') fun m n hmn => ?_
    obtain ⟨w, hw⟩ := hcau m n hmn
    refine ⟨entO Ch X w e e', X.ints.hom_inj ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO, alg_entO, alg_entO, dActX_eq, dActX_eq, dActX_eq,
      ← Matrix.sub_apply, ← map_sub, hw, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul,
      Nat.cast_pow]
  choose L W hW using hent
  have hA : ∀ N e e', algebraMap X.O X.C (L e e') =
      dActX Ch X (ε N * x N) e e' + (p : X.C) ^ N * algebraMap X.O X.C (W e e' N) := by
    intro N e e'
    have h := congrArg (algebraMap X.O X.C) (hW e e' N)
    rw [RingHom.map_sub, map_mul, map_pow, map_natCast, alg_entO] at h
    linear_combination h
  refine ⟨Matrix.of fun e e' => algebraMap X.O X.C (L e e'), fun N e e' => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply, hA N, add_sub_cancel_left]
    exact le_v_pow_mul X N _
  · funext e
    rw [← sub_eq_zero]
    refine eq_zero_of_le_v X _ fun N => ?_
    obtain ⟨z0, hz0⟩ := hxN N
    obtain ⟨u, hu⟩ := (hεN N).1
    obtain ⟨z, hz⟩ : ∃ z, φ (ε N * x N) = t + (p : T.V) ^ N * z :=
      ⟨z0 + u * t + (p : T.V) ^ N * u * z0, by rw [map_mul, hu, hz0, hP]; ring⟩
    have hj : ∀ r : T.V, jX X r = algebraMap X.O X.C (X.ι r) := fun r => X.comp r
    have he := congrFun (dActX_mulVec_lieVec Ch X hst φ τ (fun a => hφ a) (ε N * x N) i) e
    rw [hz, map_add (f := _), map_mul, map_pow, map_natCast] at he
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply] at he ⊢
    have key : ∑ e', algebraMap X.O X.C (L e e') * lieVec Ch X ⟨τ, i⟩ e' - jX X t * lieVec Ch X ⟨τ, i⟩ e =
        (p : X.C) ^ N * algebraMap X.O X.C
          (∑ e', W e e' N * X.ι (Ch.uvecT ⟨τ, i⟩ e') + X.ι z * X.ι (Ch.uvecT ⟨τ, i⟩ e)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hA N, add_mul, Finset.sum_add_distrib, he, map_add (f := _), map_sum, map_mul, ← hj, mul_add, Finset.mul_sum,
        mul_assoc]
      simp only [lieVec]
      ring
    rw [key]
    exact le_v_pow_mul X N _

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitEntriesMatrixInverseClosedProof
section
open GlobalTheory.IsoTriv

namespace GlobalTheory.LimInv

variable {R V : Type} [CommRing R] [CommRing V]

def limSub (φ : R →+* V) (q : R) : Subring V where
  carrier := {t | ∀ N : ℕ, ∃ a z, φ a = t + φ q ^ N * z}
  mul_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    refine ⟨a * b, z * t + s * w + φ q ^ N * z * w, ?_⟩
    rw [map_mul, ha, hb]; ring
  one_mem' := fun N => ⟨1, 0, by simp⟩
  add_mem' := by
    intro s t hs ht N
    obtain ⟨a, z, ha⟩ := hs N
    obtain ⟨b, w, hb⟩ := ht N
    exact ⟨a + b, z + w, by rw [map_add (f := _), ha, hb]; ring⟩
  zero_mem' := fun N => ⟨0, 0, by simp⟩
  neg_mem' := by
    intro s hs N
    obtain ⟨a, z, ha⟩ := hs N
    exact ⟨-a, -z, by rw [map_neg, ha]; ring⟩

theorem inv_mem_limSub [IsDedekindDomain R] [IsDomain V] [IsDiscreteValuationRing V]
    (φ : R →+* V) (q : R) (hq0 : φ q ≠ 0) (hqu : ¬ IsUnit (φ q)) (u : Vˣ)
    (hu : (u : V) ∈ limSub φ q) : ((u⁻¹ : Vˣ) : V) ∈ limSub φ q := by
  intro N
  obtain ⟨a, z, ha⟩ := hu (N + 1)
  have hqm : φ q ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hqu
  have haU : IsUnit (φ a) := by
    by_contra h
    have h1 : φ a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 h
    have h2 : φ q ^ (N + 1) * z ∈ IsLocalRing.maximalIdeal V :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hqm _ (Nat.succ_pos N))
    have h3 : (u : V) ∈ IsLocalRing.maximalIdeal V := by
      have : (u : V) = φ a - φ q ^ (N + 1) * z := by rw [ha]; ring
      rw [this]; exact Ideal.sub_mem _ h1 h2
    exact ((IsLocalRing.mem_maximalIdeal _).1 h3) u.isUnit
  set w : Ideal R := (IsLocalRing.maximalIdeal V).comap φ with hw
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hqw : q ∈ w := hqm
  have hwne : w ≠ ⊥ := by
    intro h
    have : q = 0 := by rw [h] at hqw; exact (Submodule.mem_bot R).1 hqw
    exact hq0 (by rw [this, map_zero])
  have hwm : w.IsMaximal := hwp.isMaximal hwne
  have haw : a ∉ w := fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) haU
  obtain ⟨y, i, hiw, hyi⟩ := hwm.exists_inv haw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero N hq0) hϖ
  have hiV : φ i ∈ Ideal.span {ϖ} := by rw [← hϖ.maximalIdeal_eq]; exact hiw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hiV
  let b : R := y * ∑ j ∈ Finset.range n, i ^ j
  have hab : φ a * φ b = 1 - φ q ^ N * ((e⁻¹ : Vˣ) * c ^ n) := by
    have h1 : a * b = 1 - i ^ n := by
      have : a * y = 1 - i := by linear_combination hyi
      calc a * b = (a * y) * ∑ j ∈ Finset.range n, i ^ j := by ring
        _ = 1 - i ^ n := by rw [this, mul_neg_geom_sum]
    have h2 : φ a * φ b = 1 - φ i ^ n := by rw [← map_mul, h1, map_sub, map_one, map_pow]
    rw [h2, he, ← hc, mul_pow]
    have : ((e : V) * (e⁻¹ : Vˣ)) = 1 := Units.mul_inv e
    linear_combination (c ^ n * ϖ ^ n) * this
  refine ⟨b, -((u⁻¹ : Vˣ) : V) * ((e⁻¹ : Vˣ) * c ^ n) - ((u⁻¹ : Vˣ) : V) * φ q * z * φ b, ?_⟩
  have hu1 : (u : V) * ((u⁻¹ : Vˣ) : V) = 1 := Units.mul_inv u
  linear_combination ((u⁻¹ : Vˣ) : V) * hab - (((u⁻¹ : Vˣ) : V) * φ b) * ha - φ b * hu1

end GlobalTheory.LimInv

open GlobalTheory.LimInv in
theorem GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof : InvSt := by
  intro R V _ _ _ _ _ φ q hq0 hqu n M hdet hM
  classical
  let S := limSub φ q
  let M₀ : Matrix (Fin n) (Fin n) S := fun b b' => ⟨M b b', fun N => hM b b' N⟩
  have hMM : S.subtype.mapMatrix M₀ = M := by ext b b'; rfl
  have hadj : ∀ b b', M.adjugate b b' ∈ S := by
    intro b b'
    rw [← hMM, ← RingHom.map_adjugate]
    exact (M₀.adjugate b b').2
  have hdetS : M.det ∈ S := by
    rw [← hMM, ← RingHom.map_det]; exact (M₀.det).2
  set u := hdet.unit with hu
  have huS : (u : V) ∈ S := by rw [hu, IsUnit.unit_spec]; exact hdetS
  have hinv := inv_mem_limSub φ q hq0 hqu u huS
  refine ⟨((u⁻¹ : Vˣ) : V) • M.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    have : ((u⁻¹ : Vˣ) : V) * M.det = 1 := by
      rw [show M.det = (u : V) by rw [hu, IsUnit.unit_spec]]; exact Units.inv_mul u
    rw [this, one_smul]
  · intro b b' N
    have : (((u⁻¹ : Vˣ) : V) • M.adjugate) b b' ∈ S := by
      rw [Matrix.smul_apply, smul_eq_mul]; exact S.mul_mem hinv (hadj b b')
    exact this N
end

