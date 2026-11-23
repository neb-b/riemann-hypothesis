module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvAtNmulPowSelf
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvTor

theorem isHausdorff_of_projective (p : ℕ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := A)
  refine ⟨fun a ha => ?_⟩
  have hdiv : ∀ m : ℕ, (p : A) ^ m ∣ a := fun m => by
    have := CEval.dvd_of_smodEq p m (ha m)
    simpa using this
  have hcoord : ∀ x, s a x = 0 := fun x => by
    refine CEval.eq_of_forall_dvd p fun m => ?_
    obtain ⟨b, hb⟩ := hdiv m
    have : a = ((p : O) ^ m) • b := by
      rw [hb, Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, sub_zero]
    exact dvd_mul_right _ _
  have h0 : s a = 0 := Finsupp.ext hcoord
  rw [← hs a, h0, map_zero]

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] (E : MvPowerSeries σ R →ₐ[R] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    (u : τ → MvPowerSeries σ R) (hu : ∀ j, constantCoeff (u j) = 0) (ψ : MvPowerSeries τ R →+* A)
    (hC : ∀ c, ψ (C c) = algebraMap R A c) (hX : ∀ j, ψ (X j) = E (u j))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ ψ f)
    (f : MvPowerSeries τ R) : E (subst u f) = ψ f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact CEval.ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) ψ
    (fun c => by
      show E (substAlgHom hs (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = ψ (X j)
      rw [substAlgHom_X, hX])
    (fun m => by
      obtain ⟨N, hN⟩ := hE m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hψ f

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ)
    (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have e : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
    rw [e]
    have h0 : ∀ s : Fin d ⊕ Fin d,
        constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) s) = 0 := by
      rintro (s | s)
      · exact ih s
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem constantCoeff_subst_var {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (e : σ → τ)
    (f : MvPowerSeries σ R) (hf : constantCoeff f = 0) :
    constantCoeff (subst (fun i => (X (e i) : MvPowerSeries τ R)) f) = 0 := by
  have h0 : ∀ s, constantCoeff ((fun i => (X (e i) : MvPowerSeries τ R)) s) = 0 := fun s => by simp
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

theorem ev₂_at_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (g : MvPowerSeries (Fin d ⊕ Fin d) O), c.ev₂ n (at2 g (fun i => inL (nmul c.μ (p ^ n) i)) (fun i => inR (nmul c.μ (p ^ n) i))) = algebraMap O (G.A n ⊗[O] G.A n) (constantCoeff g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n g
  haveI : IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    isHausdorff_of_projective (O := O) (A := G.A n ⊗[O] G.A n) p
  have hz : ∀ i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun i => by
    rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i,
      map_zero]
  have hcont : ∀ (φ : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (m : ℕ), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O,
      (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        ((p : G.A n ⊗[O] G.A n)) ^ m ∣ (φ.comp (c.ev n)).toRingHom f := fun φ m => by
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    refine ⟨N, fun f hf => ?_⟩
    have := map_dvd φ (hN f hf)
    rwa [map_pow, map_natCast] at this
  have hL : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeLeft (S := O) (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inl i)]
        rfl)
      (hcont _) f
  have hR : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inR f) = (1 : G.A n) ⊗ₜ[O] c.ev n f := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeRight).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeRight).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeRight (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inr i)]
        rfl)
      (hcont _) f
  have hμ := c.isLaw.const
  have hu : ∀ j, constantCoeff (Sum.elim (fun i => inL (nmul c.μ (p ^ n) i))
      (fun i => inR (nmul c.μ (p ^ n) i)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
  refine eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ hu
    ((algebraMap O (G.A n ⊗[O] G.A n)).comp constantCoeff) (fun r => by simp) ?_ ?_ g
  · rintro (j | j)
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inl]
      rw [hL, hz, TensorProduct.zero_tmul]
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inr]
      rw [hR, hz, TensorProduct.tmul_zero]
  · intro m
    refine ⟨1, fun f hf => ?_⟩
    have h0 : constantCoeff f = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hf 0 (by simp)
    simp [h0]

end GlobalTheory.EvTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalization
section
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.ThickLoc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}}
  {s : X ⟶ Sp R} (T : Thick κ s) (b : T.B)

abbrev locJ : Ideal (Localization.Away b) := T.J.map (algebraMap T.B (Localization.Away b))

def locφ₀ : T.B₀ →+* Localization.Away b ⧸ locJ T b :=
  T.π.liftOfSurjective T.surj
    ⟨(Ideal.Quotient.mk (locJ T b)).comp (algebraMap T.B (Localization.Away b)), fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker x).1 hx))⟩

theorem locφ₀_π (x : T.B) :
    locφ₀ T b (T.π x) = Ideal.Quotient.mk (locJ T b) (algebraMap T.B (Localization.Away b) x) := by
  unfold locφ₀
  exact RingHom.liftOfSurjective_comp_apply _ _ _ x

@[reducible] def loc : Thick κ s where
  B := Localization.Away b
  J := locJ T b
  δ := DPLoc.dp (Submonoid.powers b) T.δ
  nil := DPLoc.isNilDP _ _ T.nil
  dp := by
    rw [IsScalarTower.algebraMap_eq R T.B (Localization.Away b)]
    exact IsDPMorphism.comp _ (DPLoc.isDPMorphism _ T.δ) T.dp
  B₀ := Localization.Away b ⧸ locJ T b
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap (locφ₀ T b) ≫ T.x
  w := by
    rw [Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    ext r
    simp only [RingHom.comp_apply, locφ₀_π]
    rw [← IsScalarTower.algebraMap_apply]

def toLoc : T ⟶ loc T b where
  φ := IsScalarTower.toAlgHom R T.B (Localization.Away b)
  φ₀ := locφ₀ T b
  comm := locφ₀_π T b
  dp := DPLoc.isDPMorphism (S := Localization.Away b) (Submonoid.powers b) T.δ
  pt := rfl

variable {T b} {S : Thick κ s} (u : T ⟶ S) (hu : IsUnit (u.φ b))

def liftφ : Localization.Away b →ₐ[R] S.B where
  toRingHom := IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R T.B (Localization.Away b)]
    exact (IsLocalization.Away.lift_eq b (g := (u.φ : T.B →+* S.B)) hu _).trans (u.φ.commutes r)

theorem liftφ_algebraMap (x : T.B) :
    liftφ u hu (algebraMap T.B (Localization.Away b) x) = u.φ x := by
  show IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
      (algebraMap T.B (Localization.Away b) x) = u.φ x
  exact IsLocalization.Away.lift_eq b hu x

theorem liftφ_dp : IsDPMorphism (DPLoc.dp (S := Localization.Away b) (Submonoid.powers b) T.δ) S.δ
    (liftφ u hu : Localization.Away b →+* S.B) := by
  have h : (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
      (u.φ : T.B →+* S.B) :=
    RingHom.ext fun x => liftφ_algebraMap u hu x
  exact DPLoc.isDPMorphism_of_comp (S := Localization.Away b) (Submonoid.powers b) T.δ S.δ _
    (by rw [h]; exact u.dp)

def liftφ₀ : Localization.Away b ⧸ locJ T b →+* S.B₀ :=
  Ideal.Quotient.lift _ (S.π.comp (liftφ u hu : Localization.Away b →+* S.B)) fun _ ha ↦
    (S.ker _).2 ((liftφ_dp u hu).1 (Ideal.mem_map_of_mem _ ha))

def lift : loc T b ⟶ S where
  φ := liftφ u hu
  φ₀ := liftφ₀ u hu
  comm _ := rfl
  dp := liftφ_dp u hu
  pt := by
    have : (liftφ₀ u hu).comp (locφ₀ T b) = u.φ₀ := RingHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := T.surj x
      rw [RingHom.comp_apply, locφ₀_π, u.comm, ← liftφ_algebraMap u hu]
      rfl
    change spMap (liftφ₀ u hu) ≫ spMap (locφ₀ T b) ≫ T.x = S.x
    rw [← Category.assoc, ← Cris.spMap_comp, this, u.pt]

theorem exists_localization : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (T : Thick κ s) (b : T.B), ∃ (T' : Thick κ s) (l : T ⟶ T'), IsUnit (l.φ b) ∧ (∀ y : T'.B, ∃ (n : ℕ) (x : T.B), y * l.φ b ^ n = l.φ x) ∧ (∀ x : T.B, l.φ x = 0 → ∃ n : ℕ, b ^ n * x = 0) ∧ ∀ (S : Thick κ s) (u : T ⟶ S), IsUnit (u.φ b) → ∃! v : T' ⟶ S, l ≫ v = u := by
  intro R _ I κ X s T b
  refine ⟨loc T b, toLoc T b, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit b
  · intro y
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers b) y
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, a, ?_⟩
    change y * algebraMap T.B (Localization.Away b) b ^ n = algebraMap T.B (Localization.Away b) a
    rw [← map_pow, show b ^ n = ↑m from hn]
    exact hm
  · intro x hx
    change algebraMap T.B (Localization.Away b) x = 0 at hx
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).1 hx
    exact ⟨n, hm⟩
  · intro S u hu
    refine ⟨lift u hu, ?_, ?_⟩
    · apply Thick.Hom.ext'
      ext c
      simp only [Thick.comp_φ]
      exact liftφ_algebraMap u hu c
    · intro v hv
      have h : (v.φ : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
          (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) := by
        ext c
        have hc : (toLoc T b ≫ v).φ c = u.φ c := by rw [hv]
        simp only [Thick.comp_φ] at hc
        show v.φ (algebraMap T.B (Localization.Away b) c) =
          liftφ u hu (algebraMap T.B (Localization.Away b) c)
        exact hc.trans (liftφ_algebraMap u hu c).symm
      apply Thick.Hom.ext'
      exact AlgHom.ext fun y ↦
        RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) h) y

end GlobalTheory.ThickLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeakSectionSmallDbarEnergy
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peak_isSecOn {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (W : Set Y) (hW : W ⊆ (A.chart i).source)
    (u : V n → ℂ) (hu : Differentiable ℂ u) :
    A.IsSecOn la W (fun j y => A.g la j i y * u (A.chart i y)) := by
  refine ⟨fun j => ?_, fun j l y hy hj hl => ?_⟩
  · have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ⊆ ovl A.chart j i :=
      fun v hv => ⟨hv.1, hW hv.2⟩
    have h1 := (A.holo_g la j i).mono hsub
    have h2 := hu.comp_differentiableOn ((A.holo_trans j i).mono hsub)
    exact h1.mul h2
  · show A.g la j i y * _ = A.g la j l y * (A.g la l i y * _)
    rw [A.g_cocycle la j l i y hj hl (hW hy)]; ring

theorem peak_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H G i p ρ c q f hρ hc hball hq hf hpeak
  obtain ⟨χ, hχs, hχsupp, hχ1⟩ := _root_.GlobalTheory.smooth_bump_chart_ball n Y ι La A i p ρ hρ hball
  obtain ⟨K0, hK0, hcut⟩ := _root_.GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le n Y ι La A C χ hχs
  set W : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ with hWdef
  set Wi : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p (ρ / 2) with hWidef
  have hWo : IsOpen W := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWio : IsOpen Wi := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWs : W ⊆ (A.chart i).source := Set.inter_subset_left
  set Z : Set Y := W \ Wi with hZdef
  have hZm : MeasurableSet Z := hWo.measurableSet.diff hWio.measurableSet
  have hZloc : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyi : y ∈ Wi := by
        by_contra h
        exact hy ⟨hyW, h⟩
      filter_upwards [hWio.mem_nhds hyi] with x hx
      rw [hχ1 x hx.1 hx.2, hχ1 y hyi.1 hyi.2]
    · have hns : y ∉ tsupport χ := fun h => hyW (hχsupp h)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hns] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hns]
  have hKc : IsCompact ((A.chart i).symm '' closedBall p ρ) :=
    (isCompact_closedBall p ρ).image_of_continuousOn ((A.chart i).continuousOn_symm.mono hball)
  have hWK : Z ∩ W ⊆ (A.chart i).symm '' closedBall p ρ := fun y hy =>
    ⟨A.chart i y, ball_subset_closedBall hy.2.2, (A.chart i).left_inv hy.2.1⟩
  have hfin : A.mu (Z ∩ W) ≠ ⊤ :=
    ((measure_mono hWK).trans_lt (ap_mu_compact A _ hKc)).ne
  have hcont : ContinuousOn (fun v => ‖f v‖ ^ 2 *
      Real.exp (-A.ph (A.kap + G) i ((A.chart i).symm v))) (closedBall p ρ) :=
    (hf.continuous.continuousOn.norm.pow 2).mul
      (((A.smooth_ph (A.kap + G) i).continuousOn.mono hball).neg.rexp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hρ.le))
  refine ⟨K0 * (M * (A.mu (Z ∩ W)).toReal), by positivity, fun k => ?_⟩
  have hu : Differentiable ℂ (fun v => f v * Complex.exp (k * q v)) :=
    hf.mul ((hq.const_mul _).cexp)
  have hsec := peak_isSecOn A (A.kap + (G + k • H)) i W hWs _ hu
  refine ⟨_, _root_.GlobalTheory.smooth_cutoff_mul_sec n Y ι La A _ W χ _ hWo hχs hχsupp hsec, ?_, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target :=
      hball (ball_subset_closedBall (ball_subset_ball (by linarith) hv))
    have hs := (A.chart i).map_target hvt
    have hr := (A.chart i).right_inv hvt
    have h1 : χ ((A.chart i).symm v) = 1 := hχ1 _ hs (by rw [hr]; exact hv)
    simp only [h1, A.g_self _ i hs, hr]
    simp
  · intro j y hy
    have hns : y ∉ tsupport χ := fun h => hy (hχsupp h)
    simp [image_eq_zero_of_notMem_tsupport hns]
  · refine (hcut (G + k • H) W Z _ hWo hχsupp hsec hZm hZloc).trans ?_
    have hbd : ∀ y ∈ Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + (G + k • H))
        (fun j y => A.g (A.kap + (G + k • H)) j i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))) y) ≤
        ENNReal.ofReal (M * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : y ∈ (A.chart i).source := hy.2.1
      have hcb : A.chart i y ∈ closedBall p ρ := ball_subset_closedBall hy.2.2
      have hout : ρ / 2 ≤ ‖A.chart i y - p‖ := by
        by_contra h
        exact hy.1.2 ⟨hs, by simpa [mem_ball, dist_eq_norm] using not_le.1 h⟩
      rw [A.nsq_chart _ _ i hs (hsec.2 _ i y hy.2 (A.mem_pick y) hs)]
      have h1 := hM _ hcb
      have h2 := hpeak _ hcb
      rw [(A.chart i).left_inv hs] at h1 h2
      rw [Real.norm_of_nonneg (by positivity)] at h1
      have h3 : c * ρ ^ 2 / 4 ≤ c * ‖A.chart i y - p‖ ^ 2 := by
        have : (ρ / 2) ^ 2 ≤ ‖A.chart i y - p‖ ^ 2 := by gcongr
        nlinarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : ‖A.g (A.kap + (G + k • H)) i i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))‖ ^ 2 *
          Real.exp (-A.ph (A.kap + (G + k • H)) i y) =
          (‖f (A.chart i y)‖ ^ 2 * Real.exp (-A.ph (A.kap + G) i y)) *
          Real.exp (-(A.ph H i y - 2 * (q (A.chart i y)).re) * k) := by
        rw [A.g_self _ i hs, one_mul, norm_mul, Complex.norm_exp, ← add_assoc,
          A.ph_add _ (k • H) i y hs, A.aap_ph_nsmul H k i hs, mul_pow, ← Real.exp_nat_mul,
          mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp
        ring
      refine e.le.trans ?_
      refine mul_le_mul h1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0
      nlinarith
    have hint := setLIntegral_mono' (μ := A.mu) (hZm.inter hWo.measurableSet) hbd
    rw [setLIntegral_const] at hint
    refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOneStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  first | exact @GlobalTheory.MultOneRealised.exists_rep_of_mult_one | exact GlobalTheory.MultOneRealised.exists_rep_of_mult_one | (intros; apply GlobalTheory.MultOneRealised.exists_rep_of_mult_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionStrictHenselisationClosedFibrePoint
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem exists_section_strictHenselisation_at_closed : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  intro hKey T E _ _ _ _ _ _ _ _ hT y _ hyT hyne q hq hqu DE _ _ actE htor
  obtain ⟨S, _, _, _, _, _, _, _, _, hmax, hflat, hloc, φ, hφ, hsh⟩ := GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt T E y
  have hKey' := hKey
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith at hKey'
  have htriv : GlobalTheory.LocAcyc.TorsorsTrivial (GlobalTheory.LocAcyc.GenFib T S) q :=
    hKey' T S hT (y.comap (algebraMap (Polynomial T) E)) φ hφ hsh hyT hyne q hq hqu
  have hMN : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors T)).comap (algebraMap E S) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hx
    exact Submonoid.mem_map.mpr ⟨t, ht, IsScalarTower.algebraMap_apply T E S t⟩
  let f : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T S :=
    IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S) hMN
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) := f.toAlgebra
  obtain ⟨act', -, htor'⟩ :=
    GlobalTheory.T.isZModTorsorFiniteProjective_baseChange (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) DE q hq actE htor
  obtain ⟨σ⟩ := (GlobalTheory.LocAcyc.torsorsTrivial_iff _ q).mp htriv _ act' htor'
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hmax, hflat, hloc, σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        DE →ₐ[GlobalTheory.LocAcyc.GenFib T E] GlobalTheory.LocAcyc.GenFib T S ⊗[GlobalTheory.LocAcyc.GenFib T E] DE).toRingHom,
    fun e => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  have hσ := σ.commutes (algebraMap (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S)
    (algebraMap E (GlobalTheory.LocAcyc.GenFib T E) e))
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hσ
  rw [hσ, RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq hMN e

end GlobalTheory.LocAcyc
end

