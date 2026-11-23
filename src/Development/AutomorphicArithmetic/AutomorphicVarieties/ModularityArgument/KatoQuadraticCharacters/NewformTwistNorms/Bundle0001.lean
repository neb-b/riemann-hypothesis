module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MemKLevOneOfMemK1G
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevelInv

open UpperTheory.V.Af.GlobalFixedVectors Matrix

theorem fixed_of_loc {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (v : V) (ho : IsOpen {k | ρ k v = v}) :
    ∀ k ∈ KLev F 2 1, (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
  classical
  have key : ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 1 T, ρ k v = v) → ∀ k ∈ KLev F 2 1,
      (∀ w ∈ T, w ∉ S → GeneralLinearGroup.map (pLoc F w) k = 1) →
      (∀ w, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) → ρ k v = v := by
    intro S T hT
    induction S using Finset.induction_on with
    | empty => exact fun k hk h1 _ => hT k (mem_KAway.2 ⟨hk, fun w hw => h1 w hw (by simp)⟩)
    | insert w S hw ih =>
      intro k hk h1 h
      have h2 := ih (k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹) (mul_mem hk (inv_mem (loc_mem w hk)))
        (fun u hu huS => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simp [pLoc_locGL_of_ne huw, h1 u hu (by simp [huw, huS])])
        (fun u => by
          by_cases huw : u = w
          · subst huw; simp [pLoc_locGL]
          · simpa [pLoc_locGL_of_ne huw] using h u)
      have h3 := h w
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h2
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (ho.mem_nhds (by simp))
  exact fun k hk h => key S S (fun k hk => hS hk) k hk (fun w hw hw' => absurd hw hw') h

theorem local_mem_principal_congruence {N : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hM : (N : w.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c)
    {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : GeneralLinearGroup.map (pLoc ℚ w) k ∈ UpperTheory.V.Sd.K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat ℚ →+* w.adicCompletionIntegers ℚ :=
    ((pLoc ℚ w).comp (Ohat ℚ).subtype).codRestrict (w.adicCompletionIntegers ℚ) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  let q := Ideal.quotientMap (I := Ideal.span {(N : ↥(Ohat ℚ))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
  have h0 : ![0, 1] ᵥ* (g.val.map (Ideal.Quotient.mk (Ideal.span {(N : ↥(Ohat ℚ))}))) = ![0, 1] := hg
  change ![0, 1] ᵥ* ((g.val.map p).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers ℚ) ^ c))) = ![0, 1]
  funext j
  have h1 := congrArg q (congrFun h0 j)
  have h2 : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (p x) := fun x => rfl
  fin_cases j <;> simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, h2] using h1

theorem mem_KLev_one_of_mem_K1G (N : ℕ) {k : GL (Fin 2) (Af ℚ)} (hk : k ∈ K1G N) : k ∈ KLev ℚ 2 1 := by
  obtain ⟨g, -, rfl⟩ := hk
  refine ⟨g, ?_, rfl⟩
  haveI : Subsingleton (↥(Ohat ℚ) ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat ℚ))}) := Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact MonoidHom.mem_ker.2 (Units.ext (Subsingleton.elim _ _))

theorem nat_mem_loc {F : Type} [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) (c : ℕ) {N : ℕ}
    (h4 : (N : 𝓞 F) ∈ q.asIdeal ^ c) :
    (N : q.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers F) ^ c := by
  have h5 : q.asIdeal.map (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) ≤ IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (q.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (q.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (q.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' q _).trans_lt ((q.valuation_lt_one_iff_mem x).2 h1)
    exact h2
  rw [← map_natCast (algebraMap (𝓞 F) (q.adicCompletionIntegers F))]
  have h6 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (q.adicCompletionIntegers F)) h4
  rw [Ideal.map_pow] at h6
  exact Ideal.pow_right_mono h5 _ h6

theorem nat_mem {M : ℕ} {w q : HeightOneSpectrum (𝓞 ℚ)} (hM : 1 ≤ M) (hd : normV w ∣ M) (hq : q ≠ w) :
    ((M / normV w : ℕ) : q.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers ℚ) ^ lev M q := by
  obtain ⟨N, hN⟩ := hd
  obtain ⟨hp, hw, -, -⟩ := places w
  have e : M / normV w = N := by rw [hN, Nat.mul_div_cancel_left _ hp.pos]
  rw [e]
  have hM0 : Ideal.span {(M : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  have h1 : q.asIdeal ^ lev M q ∣ Ideal.span {(M : 𝓞 ℚ)} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hM0) q.associates_irreducible]
    exact le_rfl
  have h2 : Ideal.span {(M : 𝓞 ℚ)} = w.asIdeal * Ideal.span {(N : 𝓞 ℚ)} := by
    rw [hw, Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hN]
  rw [h2] at h1
  have h3 : q.asIdeal ^ lev M q ∣ Ideal.span {(N : 𝓞 ℚ)} :=
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.2 (q.isMaximal.coprime_of_ne w.isMaximal
      fun h => hq (HeightOneSpectrum.ext h)))).dvd_of_dvd_mul_left h1
  have h4 : (N : 𝓞 ℚ) ∈ q.asIdeal ^ lev M q := Ideal.dvd_span_singleton.1 h3
  exact nat_mem_loc q _ h4

theorem inv_K1G : ∀ (M : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), 1 ≤ M → normV w ∣ M → ∀ φ : TR.Sm ℚ 2, IsOpen {u | TR.finRep ℚ 2 u φ = φ} → (∀ q, q ≠ w → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ q) (UpperTheory.V.Sd.K1 q (lev M q))) → φ ∈ Hi.fixd (UpperTheory.V.Sd.locSm ℚ w) (UpperTheory.V.Sd.K1 w 0) → ∀ u ∈ K1G (M / normV w), TR.finRep ℚ 2 u φ = φ := by
  intro M w hM hd φ ho hq hw u hu
  refine fixed_of_loc _ φ ho u (mem_KLev_one_of_mem_K1G _ hu) fun q => ?_
  by_cases h : q = w
  · subst h
    exact hw _ (local_mem_principal_congruence q 0 (by simp) hu)
  · exact hq q h _ (local_mem_principal_congruence q _ (nat_mem hM hd h) hu)

end GlobalTheory.NewLevelInv

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.MultisetEqOfProdEq
section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevel

private theorem ev_not_dvd_norm {a : ℕ} (h : a ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private theorem multiset_eq_of_prod_eq {c : ℂ} (hc : c ≠ 0) {B B' : Multiset ℂˣ}
    (h : (B.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod =
      (B'.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod) : B = B' := by
  have e : ∀ D : Multiset ℂˣ, (D.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod.roots =
      D.map fun b : ℂˣ => c * (b : ℂ) := fun D => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (D.map fun b : ℂˣ => c * (b : ℂ)), Multiset.map_map]
    rfl
  have h1 := (e B).symm.trans ((congrArg Polynomial.roots h).trans (e B'))
  exact Multiset.map_injective (fun a b hab => Units.ext (mul_left_cancel₀ hc hab)) h1

private theorem algSat_prod (q : ℕ) (t : ℂ) (B : Multiset ℂˣ) :
    ((algSat 2 q B).map fun b => Polynomial.X - Polynomial.C (t * b)).prod =
      (B.map fun b : ℂˣ => Polynomial.X -
        Polynomial.C ((t * (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) * (b : ℂ))).prod := by
  induction B using Multiset.induction_on with
  | empty => simp [algSat]
  | cons a B ih =>
    simp only [algSat, Multiset.map_cons, Multiset.prod_cons, Multiset.pure_def, Multiset.bind_def,
      Multiset.cons_bind, Multiset.singleton_add] at ih ⊢
    rw [ih, mul_assoc]

theorem spherical_of_normTwist : Published.StrongMultOneReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π π₀ : TR.CuspSub ℚ 2), (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧ ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) → (∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M)) → ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (Bs : Multiset ℂˣ), π.HasSat w Bs → ∃ B, π₀.HasSat w B := by
  intro hS k hk g j π π₀ hπ hπ₀ w Bs hBs
  have hk1 : 1 ≤ k := by omega
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ s
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ s
  have hM : g.M ≠ 0 := by have : 1 ≤ g.M := g.pos; omega
  have hiso : π.Iso (π₀.twist χ) := by
    refine hS ℚ 2 one_le_two π _ ?_
    filter_upwards [hπ, ev_not_dvd_norm hM] with q hq hd
    obtain ⟨B, hB, hpoly⟩ := hq
    obtain ⟨α, β, hv, hsum, hprod⟩ := hπ₀ q hd
    have htw := hv.twist (χ := χ) (hE.1 q)
    refine ⟨B, hB, ?_⟩
    have hq : Ideal.absNorm q.asIdeal = normV q := (places q).2.2.1
    have hq0 : (0 : ℝ) < normV q := by exact_mod_cast (places q).1.pos
    have hval : ((χ.val q : ℂˣ) : ℂ) = (((normV q : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [hE.2.1 q, hq, Complex.ofReal_cpow hq0.le]; simp
    set r : ℂ := (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have key : ∀ a : ℂˣ, ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) *
        ((a * χ.val q : ℂˣ) : ℂ) = r * a := fun a => by
      have : ((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
          (normV q : ℝ) ^ j * ((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV q : ℝ) ^ (-s)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        rw [hs]; push_cast; ring
      rw [hr, this, Units.val_mul, hval]; push_cast; ring
    have hrr : r * r = (normV q : ℂ) ^ (k - 1) := by
      rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
      push_cast; rfl
    have hc : ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast hq0.ne'))
        (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq0 _).ne')
    rw [algSat_prod] at hpoly
    have hBeq : B = Multiset.map (fun x => x * χ.val q) {α, β} := by
      refine multiset_eq_of_prod_eq hc ?_
      rw [hpoly, Newform.heckePoly]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
        Multiset.prod_singleton, key]
      rw [← hsum, ← hprod, ← hrr]
      simp only [Units.val_mul, Polynomial.C_mul, Polynomial.C_add]
      ring
    rw [hBeq]
    exact htw
  have h1 := (hiso.hasSat hBs).twist (χ := χ⁻¹) (HChar.UnrAt.inv (hE.1 w))
  rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h1
  exact ⟨_, h1⟩

end GlobalTheory.NewLevel

end
end

