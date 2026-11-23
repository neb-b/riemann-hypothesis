module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FibreComparison
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtAnOrthKerIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem gtAn_orth_ker_iff : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (v : Λ.A.La), (∀ v' : Λ.A.La, Λ.ε v'.y = 0 → Λ.A.EF v v' = 0) ↔ (Λ.ε v.y = 0 ∧ ∀ s : ℂ, ∃ x, IsTorusPt (Λ.ex0 (s • Λ.A.P0 v)) x ∧ ∀ v' : Λ.A.La, x (Λ.ε v'.y) = eTwoPi (-(s * Λ.A.EF v v'))) := by
  intro _ _ E _ _ _ H _ D l c O _ β _ _ b a Λ v
  obtain ⟨-, -, htor, hlam⟩ := _root_.GlobalTheory.ArcPts.GtKer.ker_iota_torus E H D l c O β b a Λ
  have hε : ∀ x : Λ.A.X, Λ.ε x = 0 ↔ x = 0 := fun x => map_eq_zero_iff _ Λ.ε.injective
  simp only [hε]
  constructor
  · intro h
    refine ⟨((Λ.A.orth_ker_iff v).1 h).1, fun s => ?_⟩
    obtain ⟨h2, h1⟩ := Λ.A.smul_periodMap_of_orthogonal_ker h s
    have hz : s • Λ.A.P0 v = ((s • Λ.A.P0 v).1, 0) := Prod.ext rfl h2
    refine ⟨fun x => eTwoPi ((s • Λ.A.P0 v).1 (Λ.ε.symm x)), ?_, fun v' => ?_⟩
    · have := htor (s • Λ.A.P0 v).1
      rwa [← hz] at this
    · have h3 : Λ.ε.symm (Λ.ε v'.y) = v'.y := Λ.ε.symm_apply_apply _
      simp only [h3, h1]
  · rintro ⟨hv, h⟩
    refine (Λ.A.orth_ker_iff_forall_smul_mem v).2 ⟨hv, fun s => ?_⟩
    obtain ⟨x, hx, -⟩ := h s
    exact hlam _ x hx

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTan

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

@[simp] theorem fst_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

@[simp] theorem snd_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem dualMapR_inl (φ : R →+* R') (a : R) : dualMapR φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a) := by
  ext <;> simp

theorem dualMapR_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)) (he : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMapR φ := RingHom.ext fun a => by
  have e : a = TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, he, dualMapR_inl, dualMapR_inl, dualMapR_eps]

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

end Dual

abbrev idealEps : Ideal (DualNumber ℂ⟦X⟧) :=
  (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))

theorem isAdicComplete_idealEps : IsAdicComplete idealEps (DualNumber ℂ⟦X⟧) :=
  have : Module.Finite ℂ⟦X⟧ (DualNumber ℂ⟦X⟧) := inferInstanceAs (Module.Finite ℂ⟦X⟧ (ℂ⟦X⟧ × ℂ⟦X⟧))
  isAdicComplete_map_of_finite _ (DualNumber ℂ⟦X⟧)

abbrev constEps : DualNumber ℂ →+* DualNumber ℂ⟦X⟧ := dualMapR (PowerSeries.C (R := ℂ))

section Jet

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def jet (F : V → ℂ) (z : V) : DualNumber ℂ := TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 z)

@[simp] theorem fst_jet (F : V → ℂ) (z : V) : (jet F z).fst = F 0 := by simp [jet]

@[simp] theorem snd_jet (F : V → ℂ) (z : V) : (jet F z).snd = fderiv ℂ F 0 z := by simp [jet]

theorem jet_mul {F G : V → ℂ} (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0) (z : V) :
    jet (fun v => F v * G v) z = jet F z * jet G z := by
  ext
  · simp
  · rw [snd_jet, fderiv_fun_mul hF hG]
    simp [TrivSqZeroExt.snd_mul, _root_.mul_comm]

theorem jet_pow {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) (n : ℕ) :
    jet (fun v => F v ^ n) z = jet F z ^ n := by
  induction n with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ← ih, ← jet_mul (hF.fun_pow n) hF]; simp only [pow_succ]

theorem jet_congr {F G : V → ℂ} (h : F =ᶠ[nhds 0] G) (z : V) : jet F z = jet G z := by
  rw [jet, jet, h.eq_of_nhds, h.fderiv_eq]

def IsJet (x : V → ℂ⟦X⟧) (z : V) (y : DualNumber ℂ⟦X⟧) : Prop :=
  (∀ n, DifferentiableAt ℂ (fun v => PowerSeries.coeff n (x v)) 0) ∧ y.fst = x 0 ∧
    ∀ n, PowerSeries.coeff n y.snd = fderiv ℂ (fun v => PowerSeries.coeff n (x v)) 0 z

variable {z : V}

theorem isJet_zero (z : V) : IsJet (fun _ => 0) z 0 := ⟨fun n => by simp, rfl, fun n => by simp⟩

theorem IsJet.add {x x' : V → ℂ⟦X⟧} {y y' : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (h' : IsJet x' z y') :
    IsJet (fun v => x v + x' v) z (y + y') := by
  refine ⟨fun n => ?_, by simp [h.2.1, h'.2.1], fun n => ?_⟩
  · simp only [map_add (f := _)]
    exact (h.1 n).fun_add (h'.1 n)
  · simp only [map_add (f := _), TrivSqZeroExt.snd_add]
    rw [fderiv_fun_add (h.1 n) (h'.1 n), h.2.2, h'.2.2, ContinuousLinearMap.add_apply]

theorem IsJet.sum {K : Type} (s : Finset K) {x : K → V → ℂ⟦X⟧} {y : K → DualNumber ℂ⟦X⟧}
    (h : ∀ i ∈ s, IsJet (x i) z (y i)) : IsJet (fun v => ∑ i ∈ s, x i v) z (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isJet_zero z
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsJet.const_mul {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (r : ℂ⟦X⟧) :
    IsJet (fun v => r * x v) z (TrivSqZeroExt.inl r * y) := by
  refine ⟨fun n => ?_, by simp [h.2.1], fun n => ?_⟩
  · simp only [PowerSeries.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ => (h.1 _).const_mul _
  · have e : (TrivSqZeroExt.inl r * y : DualNumber ℂ⟦X⟧).snd = r * y.snd := by simp [TrivSqZeroExt.snd_mul]
    simp only [e, PowerSeries.coeff_mul]
    rw [fderiv_fun_sum fun p _ => (h.1 _).const_mul _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [fderiv_const_mul (h.1 _), h.2.2]
    rfl

theorem isJet_C {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) :
    IsJet (fun v => PowerSeries.C (F v)) z (constEps (jet F z)) := by
  refine ⟨fun n => ?_, by simp, fun n => ?_⟩
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn, hF]
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem mem_idealEps_pow {a : DualNumber ℂ⟦X⟧} {n : ℕ} (h : a ∈ idealEps ^ n) :
    PowerSeries.X ^ n ∣ a.fst ∧ PowerSeries.X ^ n ∣ a.snd := by
  rw [idealEps, ← Ideal.map_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h
  obtain ⟨c, rfl⟩ := h
  exact ⟨⟨c.fst, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩, ⟨c.snd, by
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]; simp⟩⟩

theorem isJet_of_approx {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧}
    (h : ∀ e : ℕ, ∃ x' y', IsJet x' z y' ∧ (∀ v, PowerSeries.X ^ (e + 1) ∣ x v - x' v) ∧ y - y' ∈ idealEps ^ (e + 1)) :
    IsJet x z y := by
  have key : ∀ (n : ℕ) (a b : ℂ⟦X⟧), PowerSeries.X ^ (n + 1) ∣ a - b →
      PowerSeries.coeff n a = PowerSeries.coeff n b := fun n a b hab => by
    have := PowerSeries.X_pow_dvd_iff.1 hab n (Nat.lt_succ_self n)
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨fun n => ?_, PowerSeries.ext fun n => ?_, fun n => ?_⟩
  · obtain ⟨x', y', h₁, h₂, -⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    exact h₁.1 n
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    rw [key n _ _ (h₂ 0), ← h₁.2.1]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).1)
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    rw [← h₁.2.2]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).2)

theorem IsJet.dualMapR_eq {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (m : ℤ) (f : V → ℂ⸨X⸩)
    (hf : ∀ v, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (x v) = HahnSeries.single m (1 : ℂ) * f v) (F : ℂ⸨X⸩)
    (hF : ∀ n, F.coeff n = fderiv ℂ (fun v => (f v).coeff n) 0 z) :
    dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) y = TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) := by
  have c : ∀ (g : ℂ⸨X⸩) (n : ℤ), (HahnSeries.single m (1 : ℂ) * g).coeff (n + m) = g.coeff n := fun g n => by
    rw [HahnSeries.coeff_single_mul_add, _root_.one_mul]
  refine TrivSqZeroExt.ext (by simp [h.2.1, hf]) ?_
  have e : (TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) : DualNumber ℂ⸨X⸩).snd = HahnSeries.single m (1 : ℂ) * F := by
    simp [TrivSqZeroExt.snd_mul]
  rw [e, snd_dualMapR]
  ext k
  obtain ⟨n, rfl⟩ : ∃ n, k = n + m := ⟨k - m, by ring⟩
  rw [c, hF]
  simp only [fun v => (c (f v) n).symm.trans (congrArg (fun q : ℂ⸨X⸩ => q.coeff (n + m)) (hf v).symm)]
  generalize n + m = k
  rw [LaurentSeries.coe_algebraMap]
  simp only [PowerSeries.coeff_coe]
  by_cases hk : k < 0
  · simp [hk]
  · simp only [if_neg hk]
    exact h.2.2 _

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

def TanRel (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    (ν : Out.GtPt a.D₀ (epsR ℂ)) (g : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) : Prop :=
  ∀ x, GenRelR (A := DualNumber ℂ⟦X⟧) W.w (g.s (W.e x)) (LB.pullGen _ _ _ (ν.s x) (spMap constEps))

def IsConstMul (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ)
    (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) : Prop :=
  ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z)
    (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ →
    (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e x) i) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
    ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) =
        valR (p ≫ W.P.D.toPre.famφB (W.e x) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧
      (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) *
          valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e x)) jf) (f.f jf) =
        κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB x) j₀) (s₀.f j₀)

def HasConstExp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {j : ℕ}
    (σ : Out.H0 W.P.U.LG.L j) : Prop :=
  ∃ f : ∀ y, W.P.D.toPre.SecB j y, (∀ e, W.P.U.toUnifPre.ExpandsAt e j σ f) ∧
    ∀ x : a.D₀.X, ∃ s₀ r, IsConstMul W j x s₀ (f (W.e x)) r

end GlobalTheory.ConstTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyConstPts
section
namespace GlobalTheory.ConstPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem nonempty_constPts : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , Nonempty (ConstPts W Λ) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ
  choose g x τ h₁ h₂ h₃ h₄ using fun v : Λ.A.V => exists_constPoint W Λ.u (Λ.ex0 v) v.2 (Λ.ex0_b v)
  exact ⟨⟨g, h₁, x, h₂, h₃, τ, h₄⟩⟩

end GlobalTheory.ConstPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
section
noncomputable section

namespace GlobalTheory.SpanFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts GlobalTheory.AmpleSpan
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem top_le_of_mem {K : Type} [Field K] {Z : Scheme.{0}} (x : Sp K ⟶ Z) {V : Z.Opens} (p : Sp K) (h : x p ∈ V) :
    ⊤ ≤ x ⁻¹ᵁ V := fun q _ => by
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact h

theorem exists_lift {Z Y : Scheme.{0}} (x : Y ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ x' : Y ⟶ V.toScheme, x' ≫ V.ι = x :=
  ⟨IsOpenImmersion.lift V.ι x (by rintro _ ⟨p, rfl⟩; exact ⟨⟨x p, h trivial⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_coords_of_basis (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}}
    [IsLocallyNoetherian S] {s : S ⟶ Sp B} (o : Obj D l bb s) {A : AnArc (𝓞 E)} {y : Sp ℂ⸨X⸩ ⟶ S}
    (Φ : GenPts A o.t y) (hA : AnFin A) (hΦ : Φ.Rational) (N : ℕ) [NeZero N] (hN : 4 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    (hrat : ∀ f : A.V → ℂ⸨X⸩, IsComb A N Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
      ∃ T : ℝ, IsComb A N (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T) : Nonempty (Coords Φ N) := by
  have hLB : o.t.PP.L.IsLB := o.t.PP.isLB
  have := o.proper
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hy := top_le_of_mem y _ hyU
  have : IsAffine U := hU
  obtain ⟨m, b, hb⟩ := exists_span_powOver hL.secBaseChange (objPolAV o) (N := N) (by omega) hU
  have emb : EmbedsBy (o.t.G.hom ∣_ U) b :=
    embedsBy_powOver o.t.G (hL.ample S (objPolAV o) N hN).2 hU b
      (hb _ _ (𝟙 _) _ (𝟙 _) IsPullback.of_id_fst (Fin N) (fun _ => 1) _ (Category.id_comp _) (by simp) b
        fun i => (secScal_iff_sval hLB).2 fun Z r z J _ => by rw [Category.comp_id])
  obtain ⟨g, hg⟩ := exists_lift y hy
  obtain ⟨h, e, sq⟩ := exists_isPullback_restrict o.t.G (φ := pullback.fst o.t.G.hom y)
    (f' := pullback.snd o.t.G.hom y) (g := g) (by rw [hg]; exact IsPullback.of_hasPullback _ _)
  choose b' hb' _ using fun i => existsUnique_secScal hLB (φ := fun _ : Fin N => (o.t.G.hom ⁻¹ᵁ U).ι)
    (ε := fun _ => 1) (h := h) (formEq_const (K' := Fin 1) (ε' := fun _ => (N : ℤ)) e (by simp)) (b i)
  have span := hb _ _ h _ g sq (Fin 1) (fun _ => (N : ℤ)) _ e (by simp) b' hb'
  choose f hf hf' using fun i => Φ.span N (b' i)
  have hfib : ∀ v, fib (Φ.x v) ≫ pullback.fst o.t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  have val : ∀ i v (x' : Sp ℂ⸨X⸩ ⟶ (o.t.G.hom ⁻¹ᵁ U).toScheme) (j : o.t.PP.L.ι),
      x' ≫ (o.t.G.hom ⁻¹ᵁ U).ι = (Φ.x v).left → ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR x' ((Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f i v * Φ.τ v j ^ N :=
    fun i v x' j hx hj => by
      obtain rfl : x' = fib (Φ.x v) ≫ h := by
        rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ U).ι, Category.assoc, e, hfib, hx]
      rw [← hfib] at hj
      exact (valR_of_secScal e (hb' i) _ j hj).trans (hf' i v j hj)
  have chart : ∀ v, ∃ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart hLB ((Φ.x v).left (default : PrimeSpectrum ℂ⸨X⸩))
    exact ⟨j, top_le_of_mem _ _ hj⟩
  have conv : ∀ i v, f i v ∈ Conv.convLaurent := fun i v => by
    obtain ⟨x₀, hx₀⟩ := hΦ.1 v
    obtain ⟨j, hj⟩ := chart v
    have down : ∀ V, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ V → ⊤ ≤ x₀ ⁻¹ᵁ V := fun V hV => by
      rw [← hx₀] at hV
      exact top_le_of_mem x₀ _ (hV (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial)
    obtain ⟨x₁, rfl⟩ := exists_lift x₀ (down (o.t.G.hom ⁻¹ᵁ U) (by
      have w : (Φ.x v).left ≫ o.t.G.hom = y := Over.w (Φ.x v)
      rw [← Scheme.Hom.comp_preimage, w]
      exact hy))
    have h1 := val i v _ j ((Category.assoc _ _ _).trans hx₀) hj
    have hx₁ : ⊤ ≤ x₁ ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j) :=
      fun p _ => Set.mem_iInter.2 fun _ => down _ hj (x := p) trivial
    replace h1 := (HolHom.valR_spMap _ x₁ _ hx₁ _).symm.trans h1
    have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
    rw [← div_eq_iff h2] at h1
    rw [← h1]
    exact div_mem (Subtype.prop _) (pow_mem (hΦ.2 v j hj) _)
  obtain ⟨T, hm, hc, hz⟩ := exists_no_common_zero hA (by omega) hth hli hsp f (fun i => hrat _ (hf i) (conv i))
    fun β t ht => by
      obtain ⟨c, hc⟩ := span (Φ.sig N β t)
      refine ⟨fun i => valR (𝟙 _) ⊤ (c i), fun v => ?_⟩
      obtain ⟨j, hj⟩ := chart v
      have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
      rw [← hfib] at hj
      have hw : ⊤ ≤ fib (Φ.x v) ⁻¹ᵁ LB.wchart o.t.PP.L (fun _ : Fin 1 => pullback.fst o.t.G.hom y) (fun _ => j) :=
        fun z hz => Set.mem_iInter.2 fun _ => hj hz
      refine mul_right_cancel₀ h2 ((Φ.val N β t ht v j hj).symm.trans ?_)
      refine (congrArg (valR (fib (Φ.x v)) _) (hc fun _ => j)).trans ((HolHom.valR_eq _ _ hw _).trans ?_)
      rw [Finset.sum_mul]
      refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)
      rw [_root_.mul_assoc, ← hf' i v j hj]
      refine congrArg₂ (· * ·) ?_ (HolHom.valR_eq _ _ hw _).symm
      refine (HolHom.valR_eq _ _ hw _).symm.trans ((HolHom.valR_appLE _ _ ⊤ _ le_top _ hw).trans ?_)
      rw [fib, pullback.lift_snd]
  exact ⟨⟨T, U, hU, hy, m, b, emb, fun i v => ⟨f i v, hm i v⟩, hc, val, hz⟩⟩

theorem nonempty_coords : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) , AnFin A → Φ.Rational → ∀ (N : ℕ) [NeZero N], 4 ≤ N → Nonempty (Coords Φ N) := by
  intro hL _ E _ _ _ H _ D l B _ bb S _ s o A y Φ hA hΦ N _ hN
  obtain ⟨n, α, th, -, hth, hli, -, hsp⟩ := AnArc.exists_basis_FSum _ A hA N
  exact nonempty_coords_of_basis hL o Φ hA hΦ N hN hth hli hsp (exists_isComb_halfRing _ A hA N)

end GlobalTheory.SpanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValEqMulSvalSig
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecTransport

variable {X Z : Scheme.{0}}

abbrev valH {L : LB X} {m : ℕ} (σ : Out.H0 L m) {R : Type} [CommRing R] (x : Sp R ⟶ X) (i : L.ι) : R :=
  valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i))

theorem exists_pull {L L' : LB X} (h : L = L') (hL : L'.IsLB) {m : ℕ} (σ : Out.H0 L m) (π : Z ⟶ X) :
    ∃ s : SecP L' π m,
      (∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X) (i : L.ι) (i' : L'.ι), p ≫ π = x → HEq i i' →
        ⊤ ≤ x ⁻¹ᵁ L'.U i' → ArcPts.sval s p i' = valH σ x i) ∧
      ∀ (A K : Type) [CommRing A] [IsLocalRing A] [Field K] (ρ : A →+* K) (x : Sp A ⟶ X) (p : Sp K ⟶ Z)
        (τ : L.ι → A) (τ' : L'.ι → K) (f : K), p ≫ π = spMap ρ ≫ x → IsFrm L' (p ≫ π) τ' →
        (∀ i i', HEq i i' → ⊤ ≤ x ⁻¹ᵁ L.U i → τ' i' = ρ (τ i)) →
        (∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → ρ (valH σ x i) = f * ρ (τ i) ^ m) → HasVal s p τ' f := by
  subst h
  have ex : ∀ π' : Z ⟶ X, π' = π ≫ 𝟙 X → ∃ s : SecP L π' m, ∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X)
      (i : L.ι), p ≫ π = x → ⊤ ≤ x ⁻¹ᵁ L.U i → ArcPts.sval s p i = valH σ x i := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => (m : ℤ)) σ π, fun R _ p x i hx hi => ?_⟩
    subst hx
    exact (HolHom.valR_res p _ _ (GenericPoints.le_wchart hi)).trans (HolHom.valR_comp p π _ _).symm
  obtain ⟨s, hs⟩ := ex π (Category.comp_id _).symm
  refine ⟨s, fun R _ p x i i' hx hi hi' => ?_, fun A K _ _ _ ρ x p τ τ' f hp hτ h₁ h₂ => ?_⟩
  · obtain rfl := eq_of_heq hi
    exact hs R p x i hx hi'
  · obtain ⟨i, hi⟩ := GenericPoints.exists_chart_loc hL x
    have hi' := FormalValue.top_le_comp hi (spMap ρ)
    refine GenericPoints.hasVal_of_chart s p hτ (j := i) (hp ▸ hi') ?_
    rw [hs K p _ i hp hi', h₁ i i HEq.rfl hi, ← h₂ i hi]
    exact HolHom.valR_spMap ρ x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i))
      (fun _ hz => Set.mem_iInter.2 fun _ => hi hz) _

end SecTransport

theorem secVal_eq_mul_sval_sig : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (j : ℕ) [NeZero j] (α : Λ.A.X) (th : (Fin Λ.A.gB → ℂ) → ℂ) (r : ℂ⸨X⸩) (σ : Out.H0 W.P.U.LG.L j), Ξ.IsGen Φ → th ∈ Λ.A.Theta j α → Ξ.Vals σ (fun v => r * Λ.A.FSum j α th v) → ∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (i : W.t.PP.L.ι), HEq jL i → ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U i → FormalValue.secVal (S := ℂ⸨X⸩) W.P.U.toUnifPre σ q.left jL = r * sval (Φ.sig j α th) (fib q) i := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ j _ α th r σ hgen hth hval q jL i hi hq
  obtain ⟨s, hs₁, hs₂⟩ := SecTransport.exists_pull (congrArg RigLB.L W.P.bundle) W.t.PP.isLB σ
    (pullback.fst W.t.G.hom gen)
  have hfib : ∀ p : Over.mk gen ⟶ W.t.G, fib p ≫ pullback.fst W.t.G.hom gen = p.left := fun p =>
    pullback.lift_fst _ _ _
  have hv : ∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (r * Λ.A.FSum j α th v) := fun v =>
    hs₂ ℂ⟦X⟧ ℂ⸨X⸩ (algebraMap _ _) (Ξ.x v).left (fib (Φ.x v)) (Ξ.τ v) (Φ.τ v) _ ((hfib _).trans (hgen v).1)
      (by rw [hfib]; exact Φ.frm v) (hgen v).2 (hval v)
  have hq₂ : fib q ≫ pullback.snd W.t.G.hom gen = spMap (RingHom.id _) := by
    rw [fib, pullback.lift_snd]
    exact (Spec.map_id _).symm
  have key := sval_eq_sum_of_hasVal E H _ Λ.A W.t gen Φ j s 1 (fun _ => r) (fun _ => α) (fun _ => th) (fun _ => hth)
    (fun v => by rw [Fin.sum_univ_one]; exact hv v) ℂ⸨X⸩ (RingHom.id _) (fib q) hq₂ i (by rw [hfib]; exact hq)
  rw [Fin.sum_univ_one] at key
  exact (hs₁ _ (fib q) q.left jL i (hfib q) hi hq).symm.trans key

end GlobalTheory.ArcPts
end
end

