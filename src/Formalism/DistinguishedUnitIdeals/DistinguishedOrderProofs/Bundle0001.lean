module

public import Mathlib
public import Formalism.DistinguishedUnitIdeals.Bundle0001

@[expose] public section

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.AevalApplySubEvalOneMem
section
noncomputable section

namespace Formalism.ExponentWindows

theorem pow_apply_sub_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (n : ℕ) : (γ ^ n) w - w ∈ U := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := hU _ ih
    have e0 : (γ ^ (n + 1)) w = γ ((γ ^ n) w) := by rw [pow_succ']; rfl
    have e : (γ ^ (n + 1)) w - w = γ ((γ ^ n) w - w) + (γ w - w) := by
      rw [e0, map_sub]; abel
    rw [e]
    exact U.add_mem h1 hw

theorem aeval_apply_sub_eval_one_mem {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (γ : Module.End R M) (U : Submodule R M) (hU : ∀ u ∈ U, γ u ∈ U) (w : M)
    (hw : γ w - w ∈ U) (P : Polynomial R) :
    Polynomial.aeval γ P w - P.eval 1 • w ∈ U := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval γ (p + q) w - (p + q).eval 1 • w =
        (Polynomial.aeval γ p w - p.eval 1 • w) + (Polynomial.aeval γ q w - q.eval 1 • w) := by
      rw [map_add (f := _), LinearMap.add_apply, Polynomial.eval_add, add_smul]; abel
    rw [e]
    exact U.add_mem hp hq
  | monomial n a =>
    have e : Polynomial.aeval γ (Polynomial.monomial n a) w - (Polynomial.monomial n a).eval 1 • w =
        a • ((γ ^ n) w - w) := by
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one, smul_sub]
      congr 1
      all_goals first
        | rfl
        | simp [Module.algebraMap_end_apply]
    rw [e]
    exact U.smul_mem a (pow_apply_sub_mem γ U hU w hw n)

theorem aeval_sub_eval_one_smul_mem : KillerShift := by
  intro R M _ _ _ γ U hU P w hw
  exact aeval_apply_sub_eval_one_mem γ U hU w hw P

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Descent
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O]

theorem algHom_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (a : O) : φ (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using φ.commutes a

theorem algHom_eq_const_add (φ : PowerSeries O →ₐ[O] PowerSeries O) (h : PowerSeries O) :
    φ h = C (constantCoeff h) + φ X * φ (mk fun p => coeff (p + 1) h) := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const h]
  rw [map_add (f := _), map_mul, algHom_C]
  ring

theorem order_map_toNat_of_isDistinguishedAt {I : Ideal O} (hI : I ≠ ⊤) {E : Polynomial O}
    (hE : E.IsDistinguishedAt I) :
    ((E : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = E.natDegree := by
  have h := hE.coe_natDegree_eq_order_map (E : PowerSeries O) 1
    (by rw [map_one]; exact (Ideal.ne_top_iff_one I).mp hI) (by rw [mul_one])
  rw [← h, ENat.toNat_coe]

theorem exists_div_of_isDistinguishedAt {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) (F : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < E.natDegree ∧
      F = (E : PowerSeries O) * q + r := by
  have H := hE.isWeierstrassDivisorAt hI
  have hd := H.isWeierstrassDivisionAt_div_mod F
  refine ⟨H.div F, H.mod F, ?_, hd.eq_mul_add⟩
  have h1 := hd.degree_lt
  rwa [order_map_toNat_of_isDistinguishedAt hI hE] at h1

theorem eq_zero_of_isDistinguishedAt_mul {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) {q : PowerSeries O} {r : Polynomial O}
    (hr : r.degree < E.natDegree) (h : (E : PowerSeries O) * q = r) : r = 0 := by
  have H := hE.isWeierstrassDivisorAt hI
  refine (H.eq_zero_of_mul_eq ?_ h).2
  rwa [order_map_toNat_of_isDistinguishedAt hI hE]

theorem coe_sum_fin {d : ℕ} (a : Fin d → O) :
    ((∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) :
      PowerSeries O) = ∑ i : Fin d, C (a i) * X ^ (i : ℕ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i : Fin d => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) Finset.univ
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X] at h
  exact h

theorem coeff_sum_fin {d : ℕ} (a : Fin d → O) (j : Fin d) :
    (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).coeff j = a j := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]

theorem coe_eq_sum_fin {d : ℕ} {r : Polynomial O} (hr : r.degree < d) :
    (r : PowerSeries O) = ∑ i : Fin d, C (r.coeff i) * X ^ (i : ℕ) := by
  have h : r = ∑ i : Fin d, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ) := by
    ext j
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < d
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr (by exact_mod_cast not_lt.mp hj))]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact hj (h ▸ i.2)
  rw [← coe_sum_fin]
  exact congrArg _ h

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {P : R} (hP : ¬ IsUnit P) {x : R} (h : ∀ N : ℕ, P ^ N ∣ x) : x = 0 := by
  have hI : Ideal.span {P} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have h0 := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hx : x ∈ ⨅ i, Ideal.span {P} ^ i := Ideal.mem_iInf.mpr fun N => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h N
  rw [h0, Ideal.mem_bot] at hx
  exact hx

theorem exists_sum_algHom_mul_X_pow (φ : PowerSeries O →ₐ[O] PowerSeries O) (d : ℕ)
    (hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r)
    (hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0)
    (F : PowerSeries O) : ∃ h : Fin d → PowerSeries O, F = ∑ i, φ (h i) * X ^ (i : ℕ) := by
  choose qf rf hrf hF using hdiv
  let H : PowerSeries O → Fin d → PowerSeries O := fun F i => mk fun k => (rf (qf^[k] F)).coeff i
  have hT : ∀ G i, (mk fun p => coeff (p + 1) (H G i)) = H (qf G) i := by
    intro G i
    ext p
    simp [H, PowerSeries.coeff_mk, Function.iterate_succ_apply]
  have hc : ∀ G i, constantCoeff (H G i) = (rf G).coeff i := by
    intro G i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    rfl
  have hS : ∀ G, ∑ i, φ (H G i) * X ^ (i : ℕ) = rf G + φ X * ∑ i, φ (H (qf G) i) * X ^ (i : ℕ) := by
    intro G
    rw [coe_eq_sum_fin (hrf G), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algHom_eq_const_add φ (H G i), hc, hT]
    ring
  have hdvd : ∀ N G, φ X ^ N ∣ G - ∑ i, φ (H G i) * X ^ (i : ℕ) := by
    intro N
    induction N with
    | zero => intro G; simp
    | succ N ih =>
      intro G
      obtain ⟨c, hc'⟩ := ih (qf G)
      refine ⟨c, ?_⟩
      rw [hS G]
      linear_combination (hF G) + φ X * hc'
  refine ⟨H F, ?_⟩
  exact (sub_eq_zero.mp (hkrull _ fun N => hdvd N F))

theorem eq_zero_of_sum_algHom_mul_X_pow [IsDomain O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (d : ℕ)
    (huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0)
    (hP0 : φ X ≠ 0) :
    ∀ (n : ℕ) (h : Fin d → PowerSeries O), ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      ∀ i, coeff n (h i) = 0 := by
  have step : ∀ h : Fin d → PowerSeries O, ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      (∀ i, constantCoeff (h i) = 0) ∧
        ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) = 0 := by
    intro h hs
    have e : ∑ i, φ (h i) * X ^ (i : ℕ) = ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) +
        φ X * ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algHom_eq_const_add φ (h i)]
      ring
    rw [hs] at e
    have h0 := huniq (fun i => constantCoeff (h i))
      (-(∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ))) (by linear_combination -e)
    refine ⟨h0, ?_⟩
    have hsum0 : ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show constantCoeff (h i) = 0 from h0 i, map_zero, zero_mul]
    rw [hsum0, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hP0
  intro n
  induction n with
  | zero =>
    intro h hs i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (step h hs).1 i
  | succ n ih =>
    intro h hs i
    have h1 := ih _ (step h hs).2 i
    simpa [PowerSeries.coeff_mk] using h1

end Helpers

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

theorem C_dvd_of_forall_dvd_coeff (a : O) (w : PowerSeries O) (h : ∀ n, a ∣ coeff n w) :
    C a ∣ w := by
  choose q hq using h
  refine ⟨PowerSeries.mk q, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hq n

theorem C_dvd_of_C_dvd_mul (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (f w : PowerSeries O)
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f ≠ 0)
    (h : C ϖ ∣ f * w) : C ϖ ∣ w := by
  obtain ⟨q, hq⟩ := h
  have hk : Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have h0 : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (f * w) = 0 := by
    rw [hq, map_mul, PowerSeries.map_C, hk, map_zero, zero_mul]
  rw [map_mul] at h0
  have hw : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w = 0 :=
    (mul_eq_zero.mp h0).resolve_left hf
  apply C_dvd_of_forall_dvd_coeff
  intro n
  have hn := congrArg (PowerSeries.coeff n) hw
  rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hn
  exact hn

theorem map_ne_zero_of_unitDist (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (d : ℕ)
    (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p ≠ 0 := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  subst hdeg
  rw [map_mul]
  refine mul_ne_zero (hu.map _).ne_zero ?_
  intro h0
  have hc := congrArg (PowerSeries.coeff E.natDegree) h0
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, hE.monic.coeff_natDegree, map_one, map_zero] at hc
  exact one_ne_zero hc

theorem constantCoeff_mem_of_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p)
    (hd : 1 ≤ d) : coeff 0 p ∈ Ideal.span {ϖ} := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := hp
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  exact hE.mem (by omega)

end Helpers

private theorem mem_span_of_C_pow_mul_mem_span {O : Type} [CommRing O] [IsDomain O] (ϖ : O)
    [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0) (q : PowerSeries O)
    (hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q ≠ 0) :
    ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {q} → z ∈ Ideal.span {q} := by
  have hC : (C ϖ : PowerSeries O) ≠ 0 := fun h =>
    hϖ0 (by simpa using congrArg PowerSeries.constantCoeff h)
  intro N
  induction N with
  | zero =>
    intro z hz
    simpa using hz
  | succ N ih =>
    intro z hz
    apply ih
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨y, hy⟩ := hz
    have hdiv : C ϖ ∣ q * y := ⟨C (ϖ ^ N) * z, by rw [← hy, pow_succ, map_mul]; ring⟩
    obtain ⟨y', rfl⟩ := C_dvd_of_C_dvd_mul ϖ q y hq hdiv
    refine ⟨y', ?_⟩
    apply mul_left_cancel₀ hC
    rw [pow_succ, map_mul] at hy
    linear_combination hy

theorem mem_span_pow_of_uniformizer_mul : SatDist := by
  intro O _ _ _ ϖ hϖ d p hp k N z hz
  have := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have hq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (p ^ k) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero k (map_ne_zero_of_unitDist ϖ d p hp)
  exact mem_span_of_C_pow_mul_mem_span ϖ hϖ.ne_zero (p ^ k) hq N z hz

theorem pow_dvd_of_const_mem_span : ConstDist := by
  intro O _ _ _ ϖ hϖ d p hp hd c y N a h
  have key : ∀ (N : ℕ) (z : PowerSeries O), C (ϖ ^ N) * z ∈ Ideal.span {p} → z ∈ Ideal.span {p} :=
    fun N z hz => by simpa using mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp 1 N z (by simpa using hz)
  have hp0 := constantCoeff_mem_of_unitDist ϖ d p hp hd
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, Ideal.mem_span_singleton] at hp0
  have h1 := key N _ h
  clear h
  induction y generalizing c a with
  | zero => simp
  | succ y ih =>
    have e2 : C (ϖ ^ y) * (C ϖ * a) = C (ϖ ^ (y + 1)) * a := by
      rw [← mul_assoc, ← map_mul, pow_succ]
    have h2 : C c - C (ϖ ^ y) * (C ϖ * a) ∈ Ideal.span {p} := by
      rw [e2]
      exact h1
    obtain ⟨c', rfl⟩ := ih c (C ϖ * a) h2
    have e3 : C (ϖ ^ y) * (C c' - C ϖ * a) = C (ϖ ^ y * c') - C (ϖ ^ (y + 1)) * a := by
      rw [mul_sub, ← map_mul, ← mul_assoc, ← map_mul, ← pow_succ]
    have h3 : C c' - C ϖ * a ∈ Ideal.span {p} := by
      apply key y
      rw [e3]
      exact h1
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h3
    have h4 := congrArg PowerSeries.constantCoeff hg
    simp only [map_mul, map_sub, PowerSeries.constantCoeff_C] at h4
    have hc' : ϖ ∣ c' := by
      have e : c' = PowerSeries.constantCoeff g * PowerSeries.constantCoeff p +
          ϖ * PowerSeries.constantCoeff a := by
        linear_combination (-1 : O) * h4
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right hp0 _) (dvd_mul_right _ _)
    obtain ⟨c'', rfl⟩ := hc'
    exact ⟨c'', by ring⟩

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfNoDown
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

theorem lam_eq_pow_mul {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ)
    (hs : s < ell) :
    abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t := by
  unfold abelian₂
  rw [← Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t) (Finset.mem_range.mpr hs)]

theorem levelCond_of_sub_pow_smul {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (P : PowerSeries O)
    (H b : ℕ) (k : Kind) (hk : k ≠ Kind.down) (V : Submodule O (Fin r → O))
    (y w : Fin r → PowerSeries O) (m : ℕ)
    (h : LevelCond ϖ P H b k V (C (ϖ ^ m) • y - P ^ H • w)) :
    LevelCond ϖ P H b k V y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N + m, z + C (ϖ ^ N) • w, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, ← hz, smul_sub, smul_comm (P ^ H) (C (ϖ ^ N)) w]
    abel
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    refine ⟨N + m, c, z + C (ϖ ^ N) • w, hc, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, smul_comm (P ^ H) (C (ϖ ^ N)) w, ← add_assoc, ← hz,
      smul_sub]
    abel
  | down => exact absurd rfl hk

theorem levels_mod_const_iff_of_no_down : MNone := by
  intro O _ _ _ ϖ _ ℓ ell r p H b kind V _ _ _ _ hnd y
  constructor
  · intro hII s hs
    obtain ⟨d, k, hd⟩ := hII s hs
    rw [lam_eq_pow_mul p H ell s hs, mul_smul] at hd
    exact levelCond_of_sub_pow_smul ϖ (p s) (H s) (b s) (kind s) (hnd s hs) (V s) y _ k hd
  · intro hNN s hs
    refine ⟨0, 0, ?_⟩
    have h0 : (cst (0 : Fin r → O) : Fin r → PowerSeries O) = 0 := by
      funext i; simp [cst]
    simpa [h0] using hNN s hs

end Formalism.ExponentWindows
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.UnivPart
section
noncomputable section

namespace Formalism.ExponentWindows

open Module

section Lattice

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} {r : ℕ}

lemma mem_of_pow_smul_mem (S : Submodule O (Fin r → O)) (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S)
    (n : ℕ) (v : Fin r → O) (h : ϖ ^ n • v ∈ S) : v ∈ S := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply hS
    rw [smul_smul, ← pow_succ']
    exact h

lemma quotient_isTorsionFree (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : IsTorsionFree O ((Fin r → O) ⧸ S) := by
  have hnz : ∀ (c : O) (v : Fin r → O), c ≠ 0 → c • v ∈ S → v ∈ S := by
    intro c v hc hcv
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
    obtain ⟨u, hu⟩ := hn
    apply mem_of_pow_smul_mem S hS n v
    rw [← hu, mul_comm, mul_smul]
    exact S.smul_mem _ hcv
  constructor
  intro c hc x y hxy
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [← Submodule.Quotient.mk_smul] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  rw [← smul_sub] at hxy
  exact hnz c _ hc.ne_zero hxy

lemma exists_isCompl_of_saturated (hϖ : Irreducible ϖ) (S : Submodule O (Fin r → O))
    (hS : ∀ v : Fin r → O, ϖ • v ∈ S → v ∈ S) : ∃ Q : Submodule O (Fin r → O), IsCompl S Q := by
  have := quotient_isTorsionFree hϖ S hS
  have : Module.Free O ((Fin r → O) ⧸ S) := Module.free_of_finite_type_torsion_free'
  obtain ⟨h, hh⟩ := Module.projective_lifting_property S.mkQ (LinearMap.id) S.mkQ_surjective
  refine ⟨LinearMap.range h, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hxS ⟨q, rfl⟩
    have hq : q = 0 := by
      have := LinearMap.congr_fun hh q
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [← this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxS
    simp [hq]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x - h (S.mkQ x) ∈ S := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← Submodule.mkQ_apply,
        ← Submodule.mkQ_apply]
      have := LinearMap.congr_fun hh (S.mkQ x)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      rw [this, sub_self]
    have : x = (x - h (S.mkQ x)) + h (S.mkQ x) := by abel
    rw [this]
    exact Submodule.add_mem_sup hx (LinearMap.mem_range_self h _)

end Lattice

end Formalism.ExponentWindows
end
end

