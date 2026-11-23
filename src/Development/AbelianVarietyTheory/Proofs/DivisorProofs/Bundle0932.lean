module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import GroundTheory.Brauer.SkolemNoether
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFins
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem infGL_mem_supS {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w _
  have h := pFin_infGL (E := E) (a := a) y
  ext i j
  have := congrArg (fun z : GL (Fin a) (Af E) => (pLoc E w) ((z : Matrix (Fin a) (Fin a) (Af E)) i j)) h
  simpa [Matrix.one_apply, apply_ite] using this

theorem locSpan_rightInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a),
    GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) →
    (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  intro E _ _ _ a S F₀ k hInf hS hF₀
  let V : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ g, F (g * k) = F g}
      add_mem' := fun {F G} hF hG g => by simp only [Pi.add_apply, hF g, hG g]
      zero_mem' := fun _ => rfl
      smul_mem' := fun c F hF g => by simp only [Pi.smul_apply, hF g] }
  have hc : ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, h * k = k * h := fun h hh => GlobalTheory.T.adelicGL_complementary_supports_commute E a S h k hh hInf hS
  refine fun F hF => (locSpan_le (V := V) hF₀ ?_ ?_) hF
  · intro F hF h hh g
    show F (g * k * h) = F (g * h)
    rw [mul_assoc, ← hc h hh, ← mul_assoc, hF]
  · intro F hF X _ ν _ k' γ _ g
    show GlobalTheory.JSW.kerInf ν k' γ F (g * k) = GlobalTheory.JSW.kerInf ν k' γ F g
    unfold GlobalTheory.JSW.kerInf
    congr 1
    funext x
    rw [mul_assoc, ← hc _ (infGL_mem_supS S (γ x)), ← mul_assoc, hF]

end GlobalTheory.JSW.MirSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilMeasureOfCongruentForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFinOver

theorem liesOver_comp_complexConj_of_not_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p)
    (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ →
      LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  intro p _ G ψ h x
  exact (GlobalTheory.HTGroupOver.liesOver_or_conj p G ψ).resolve_left h x

end GlobalTheory.StabFinOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact _root_.GlobalTheory.LKRes.sigKQ_iterate_self p K r hr _

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupport
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
namespace GlobalTheory.SimBound

theorem eq_one_of_forall_prime {r : ℚ} (hr : 0 < r)
    (h : ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ)) : r = 1 := by
  have hn : r.num.natAbs = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).1 (Int.natCast_dvd.2 hqd)
  have hd : r.den = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    exact (h q hq).2 (Int.natCast_dvd_natCast.2 hqd)
  have hpos : 0 < r.num := Rat.num_pos.2 hr
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hd]; simp

theorem not_dvd_of_iff {r : ℚ} {q : ℕ} (hq : q.Prime) (h : (q : ℤ) ∣ r.num ↔ (q : ℤ) ∣ (r.den : ℤ)) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have key : ¬ ((q : ℤ) ∣ r.num ∧ (q : ℤ) ∣ (r.den : ℤ)) := by
    rintro ⟨h1, h2⟩
    have h1' : q ∣ r.num.natAbs := Int.natCast_dvd.1 h1
    have h2' : q ∣ r.den := Int.natCast_dvd_natCast.1 h2
    have h3 : q ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1' h2'
    rw [r.reduced.gcd_eq_one] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
  exact ⟨fun h1 => key ⟨h1, h.1 h1⟩, fun h2 => key ⟨h.2 h2, h2⟩⟩

theorem not_dvd_of_padicNorm (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : padicNorm p r = 1) :
    ¬ (p : ℤ) ∣ r.num ∧ ¬ (p : ℤ) ∣ (r.den : ℤ) := by
  have e : padicNorm p (r.num : ℚ) = padicNorm p ((r.den : ℤ) : ℚ) := by
    rw [← Rat.mul_den_eq_num, padicNorm.mul, hr, one_mul, Int.cast_natCast]
  refine not_dvd_of_iff (Fact.out : p.Prime) ?_
  rw [← padicNorm.int_lt_one_iff, ← padicNorm.int_lt_one_iff, e]

theorem not_dvd_of_valuation {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum ℤ)
    (hv : v.asIdeal = Ideal.span {(q : ℤ)}) {r : ℚ} (hr : v.valuation ℚ r = 1) :
    ¬ (q : ℤ) ∣ r.num ∧ ¬ (q : ℤ) ∣ (r.den : ℤ) := by
  have e : v.valuation ℚ (algebraMap ℤ ℚ r.num) = v.valuation ℚ (algebraMap ℤ ℚ (r.den : ℤ)) := by
    rw [algebraMap_int_eq, eq_intCast, eq_intCast, ← Rat.mul_den_eq_num, map_mul, hr, one_mul,
      Int.cast_natCast]
  refine not_dvd_of_iff hq ?_
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, ← hv, ← valuation_lt_one_iff_mem (K := ℚ),
    ← valuation_lt_one_iff_mem (K := ℚ), e]

def placeOf (p : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(q : ℤ)}, (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hq), by simpa using hq.ne_zero⟩, fun h => hqp (by
    have h1 := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := Int.natAbs_eq_natAbs_iff.2 (Int.associated_iff.1 h1)
    simpa using h2)⟩

theorem eq_one_of_units (p : ℕ) [Fact p.Prime] {r : ℚ} (hr : 0 < r)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) r) = 1) (hp : padicNorm p r = 1) :
    r = 1 := by
  refine eq_one_of_forall_prime hr fun q hq => ?_
  by_cases hqp : q = p
  · subst hqp; exact not_dvd_of_padicNorm q hp
  · refine not_dvd_of_valuation hq (placeOf p hq hqp).1 rfl ?_
    rw [← valuedAdicCompletion_eq_valuation']
    exact hw (placeOf p hq hqp)

theorem valued_snd_eq_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Subgroup G.GAf)
    (hK : IsCompact (K : Set G.GAf)) (w : AwayP p) {k : G.GAf} (hk : k ∈ K) :
    Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) = 1 := by
  letI : NontriviallyNormedField (w.1.adicCompletion ℚ) := Valued.toNontriviallyNormedField _ _
  let F : G.GAf → ℝ := fun g => ‖AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)‖
  have hev : Continuous (fun x : AfP p => AfP.eval w x) :=
    RestrictedProduct.continuous_eval (R := fun v : AwayP p => v.1.adicCompletion ℚ)
      (A := fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) w
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  have hF : Continuous F :=
    continuous_norm.comp (hev.comp (Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hmul : ∀ a b : G.GAf, F (a * b) = F a * F b := fun a b => by
    simp only [F, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul, norm_mul]
  have hone : F 1 = 1 := by simp [F]
  have hpow : ∀ (a : G.GAf) (n : ℕ), F (a ^ n) = F a ^ n := fun a n => by
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hle : ∀ a ∈ K, F a ≤ 1 := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC (a ^ n) (K.pow_mem ha n)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have : F (a ^ n) = F a ^ n := hpow a n
    linarith
  have h1 := hle k hk
  have h2 := hle k⁻¹ (K.inv_mem hk)
  have h3 : F k⁻¹ * F k = 1 := by rw [← hmul, inv_mul_cancel, hone]
  have h0 : 0 ≤ F k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ F k := norm_nonneg _
  have hk1 : F k = 1 := by nlinarith
  have hle1 : Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.1 hk1.le
  have hnlt : ¬ Valued.v (AfP.eval w (((k : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p)) < 1 :=
    fun h => by
      have := Valued.toNormedField.norm_lt_one_iff.2 h
      exact absurd hk1 (ne_of_lt this)
  exact le_antisymm hle1 (not_lt.1 hnlt)

noncomputable def nu1 (p : ℕ) [Fact p.Prime] (g : GL (Fin 1) (Qr p 1)) : ℝ :=
  ‖(((g : Matrix (Fin 1) (Fin 1) (Qr p 1)) 0 0 : Qr p 1) : PadicAlgCl p)‖

theorem glOneUnramifiedEntryNorm_mul (p : ℕ) [Fact p.Prime] (a b : GL (Fin 1) (Qr p 1)) : nu1 p (a * b) = nu1 p a * nu1 p b := by
  simp only [nu1, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one, IntermediateField.coe_mul, norm_mul]

theorem glOneUnramifiedEntryNorm_one (p : ℕ) [Fact p.Prime] : nu1 p 1 = 1 := by simp [nu1]

theorem glOneUnramifiedEntryNorm_le_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)} (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) :
    nu1 p k ≤ 1 := by
  obtain ⟨u, rfl⟩ := hk
  have h := ((u : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) 1)) 0 0).2
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 h

theorem glOneUnramifiedEntryNorm_eq_one_of_integral (p : ℕ) [Fact p.Prime] {k : GL (Fin 1) (Qr p 1)}
    (hk : k ∈ GlobalTheory.LKLoc.Kint p (Q0 p) 1 1) : nu1 p k = 1 := by
  have h1 := glOneUnramifiedEntryNorm_le_one_of_integral p hk
  have h2 := glOneUnramifiedEntryNorm_le_one_of_integral p ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 1).inv_mem hk)
  have h3 : nu1 p k⁻¹ * nu1 p k = 1 := by rw [← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one]
  have h0 : 0 ≤ nu1 p k⁻¹ := norm_nonneg _
  have h0' : 0 ≤ nu1 p k := norm_nonneg _
  nlinarith

theorem glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm (p : ℕ) [Fact p.Prime] (s : ℚˣ) :
    nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ((padicNorm p (s : ℚ) : ℚ) : ℝ) := by
  have e : nu1 p (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s))) = ‖(((s : ℚ) : ℚ_[p]) : PadicAlgCl p)‖ := by
    simp [nu1, GeneralLinearGroup.scalar]
  rw [e, PadicAlgCl.norm_extends, Padic.eq_padicNorm]

noncomputable def lam {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (g : G.GAf) : WithZero (Multiplicative ℤ) :=
  Valued.v (AfP.eval w (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p))

theorem lam_mul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) (a b : G.GAf) :
    lam G w (a * b) = lam G w a * lam G w b := by
  simp only [lam, Subgroup.coe_mul, Prod.snd_mul, Units.val_mul, map_mul]

theorem lam_one {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : AwayP p) : lam G w 1 = 1 := by
  simp [lam]

theorem away {p : ℕ} [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h σ k₁ k₂ : G.GAf) (hk₁ : k₁ ∈ L.K.toSubgroup)
    (hk₂ : k₂ ∈ L.K.toSubgroup) (e : h⁻¹ * toAfF G β x t hx y * h = k₁ * σ * k₂) (w : AwayP p) :
    Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) = lam G w σ := by
  have hc : IsCompact (L.K.toSubgroup : Set G.GAf) := L.compact
  have e1 : lam G w k₁ = 1 := valued_snd_eq_one G _ hc w hk₁
  have e2 : lam G w k₂ = 1 := valued_snd_eq_one G _ hc w hk₂
  have e3 := congrArg (lam G w) e
  rw [lam_mul, lam_mul, lam_mul, lam_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : lam G w (toAfF G β x t hx y) = lam G w σ := by
    rw [← e3, mul_right_comm, ← lam_mul, inv_mul_cancel, lam_one, one_mul]
  rw [← e4]
  show _ = Valued.v (AfP.eval w (algebraMap ℚ (AfP p) (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)))
  rw [AlgHom.commutes]

theorem atp {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (h σ k₁ k₂ : Gr G 1)
    (hk₁ : k₁ ∈ KHT p G.m G.n 1 G.Fw) (hk₂ : k₂ ∈ KHT p G.m G.n 1 G.Fw)
    (e : h⁻¹ * toP1 G β y * h = k₁ * σ * k₂) :
    ((padicNorm p (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℚ) : ℝ) = nu1 p σ.1 := by
  have e1 : nu1 p k₁.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₁.1
  have e2 : nu1 p k₂.1 = 1 := glOneUnramifiedEntryNorm_eq_one_of_integral p hk₂.1
  have e3 := congrArg (fun g : Gr G 1 => nu1 p g.1) e
  simp only [Prod.fst_mul, Prod.fst_inv, glOneUnramifiedEntryNorm_mul, e1, e2, one_mul, mul_one] at e3
  have e4 : nu1 p (toP1 G β y).1 = nu1 p σ.1 := by
    rw [← e3, mul_right_comm, ← glOneUnramifiedEntryNorm_mul, inv_mul_cancel, glOneUnramifiedEntryNorm_one, one_mul]
  rw [← e4]
  exact (glOneUnramifiedEntryNorm_rat_scalar_eq_padicNorm p _).symm

theorem eq_of_valuations {p : ℕ} [Fact p.Prime] {s s₀ : ℚ} (hs : 0 < s) (hs₀ : 0 < s₀)
    (hw : ∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) =
      Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀))
    (hp : padicNorm p s = padicNorm p s₀) : s = s₀ := by
  have h := eq_one_of_units p (r := s * s₀⁻¹) (mul_pos hs (inv_pos.2 hs₀)) (fun w => by
      have h0 : Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s₀) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 hs₀.ne')
      rw [map_mul, map_mul, map_inv₀, map_inv₀, hw w, mul_inv_cancel₀ h0])
    (by
      have h0 : padicNorm p s₀ ≠ 0 := fun h => hs₀.ne' (padicNorm.zero_of_padicNorm_eq_zero h)
      rw [← div_eq_mul_inv, padicNorm.div, hp, div_self h0])
  exact (mul_inv_eq_one₀ hs₀.ne').1 h

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1),
      f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 →
      (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  intro p _ G L f hf K' f' hf' β x t hx
  obtain ⟨T, hT⟩ := hf.2.2.2
  obtain ⟨T', hT'⟩ := hf'.2.2.2
  let M : G.GAf → Gr G 1 → ℚ → Prop := fun σ σ' s => 0 < s ∧
    (∀ w : AwayP p, Valued.v (algebraMap ℚ (w.1.adicCompletion ℚ) s) = lam G w σ) ∧
    ((padicNorm p s : ℚ) : ℝ) = nu1 p σ'.1
  let g : G.GAf → Gr G 1 → ℝ := fun σ σ' => if h : ∃ s, M σ σ' s then ((h.choose : ℚ) : ℝ) else 0
  have g_nonneg : ∀ σ σ', 0 ≤ g σ σ' := by
    intro σ σ'
    simp only [g]
    split_ifs with h
    · exact_mod_cast h.choose_spec.1.le
    · exact le_rfl
  refine ⟨∑ σ ∈ T, ∑ σ' ∈ T', g σ σ', ?_⟩
  intro y h₁ h₂ h1 h2
  obtain ⟨σ, hσ, k₁, hk₁, k₂, hk₂, e⟩ := hT _ h1
  obtain ⟨σ', hσ', k₁', hk₁', k₂', hk₂', e'⟩ := hT' _ h2
  have hM : M σ σ' (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
    ⟨y.2.2, fun w => away G L β x t hx y h₁ σ k₁ k₂ hk₁ hk₂ e w, atp G β y h₂ σ' k₁' k₂' hk₁' hk₂' e'⟩
  have hex : ∃ s, M σ σ' s := ⟨_, hM⟩
  have heq : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = hex.choose :=
    eq_of_valuations hM.1 hex.choose_spec.1 (fun w => by rw [hM.2.1 w, hex.choose_spec.2.1 w])
      (by exact_mod_cast hM.2.2.trans hex.choose_spec.2.2.symm)
  have hg : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) = g σ σ' := by
    simp only [g, dif_pos hex, heq]
  rw [hg]
  calc g σ σ' ≤ ∑ σ'' ∈ T', g σ σ'' :=
        Finset.single_le_sum (f := fun σ'' => g σ σ'') (fun i _ => g_nonneg σ i) hσ'
    _ ≤ ∑ σ₀ ∈ T, ∑ σ'' ∈ T', g σ₀ σ'' :=
        Finset.single_le_sum (f := fun σ₀ => ∑ σ'' ∈ T', g σ₀ σ'')
          (fun i _ => Finset.sum_nonneg fun j _ => g_nonneg i j) hσ

end GlobalTheory.SimBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjecStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_adelicProdUnramifiedEmbedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  first | (exact @GlobalTheory.LKMid.pair_embedding_injective) | (exact GlobalTheory.LKMid.pair_embedding_injective) | (intros; apply GlobalTheory.LKMid.pair_embedding_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧ (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ = ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LKMid.pair_form_laws) | (exact GlobalTheory.LKMid.pair_form_laws) | (intros; apply GlobalTheory.LKMid.pair_form_laws  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_regular_image_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G), (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧ ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  first | (exact @GlobalTheory.LKMid.atP_regular) | (exact GlobalTheory.LKMid.atP_regular) | (intros; apply GlobalTheory.LKMid.atP_regular  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkolemNoetherConjugacy
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem units_conj_of_minpoly_eq_of_irreducible : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ),
    minpoly G.F (a : G.C) = minpoly G.F (b : G.C) → Irreducible (minpoly G.F (b : G.C)) →
      ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  intro p _ G a b h hirr
  have hb : IsIntegral G.F (b : G.C) := IsIntegral.of_finite G.F _
  haveI : Fact (Irreducible (minpoly G.F (b : G.C))) := ⟨hirr⟩
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (b : G.C))) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hb)).finite
  have ha : Polynomial.aeval (a : G.C) (minpoly G.F (b : G.C)) = 0 := by rw [← h]; exact minpoly.aeval _ _
  obtain ⟨y, hy⟩ := GroundTheory.Brauer.exists_unit_conj (evalQuot _ (b : G.C) (minpoly.aeval _ _))
    (evalQuot _ (a : G.C) ha)
  refine ⟨y, ?_⟩
  have := hy (AdjoinRoot.root _)
  rwa [evalQuot_root, evalQuot_root] at this

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOn
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem EtC.etC_c2 : GlobalTheory.EtC.C2 := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    exact GlobalTheory.T.subsingleton_Ht_two_of_isDedekindDomain_of_isAlgClosed q k B hq i
  · exact GlobalTheory.T.smoothAffineCurve_tateTwistCohomology_subsingleton_of_ge_three q k B hq n i (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
section
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)


open Classical in
def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tateTwist_local_to_global_strictlyHenselian : B3 := by
  intro q Y X S f p _ _ _ _ _ i h
  exact GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y X S f p
    (fun O _ s hs => h O s hs.1)

end GlobalTheory.EtC
end

