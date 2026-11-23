module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.CjEntRel
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

private theorem cjEnt_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.cjEnt :
    UpperTheory.Gal.Int.Geo.Pl.Tj.CjEnt := by
  intro E _ _ _ n g w i k
  refine ⟨GlobalTheory.SplitPts.conjSrc_conjSrc_cm w, ?_⟩
  have hrel := cjEnt_rel g w
  have hGt : ((comp (cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ)) •
        (comp w g⁻¹).val := by
    rw [map_inv]
    calc _ = ((comp (cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
          ((comp w g).val * ((comp w g)⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, smul_mul_assoc, Matrix.one_mul]
  have h := congrFun (congrFun hGt k) i
  rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h
  rw [← (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2, h]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.ConjInt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

variable {E : Type} [Field E] [NumberField E]

private theorem val_alg (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) = u.intValuation c := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (c : E)
  rw [show (u.valuation E) (c : E) = u.intValuation c from HeightOneSpectrum.valuation_of_algebraMap u c] at h
  exact h

private theorem alg_int (u : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) :
    algebraMap (𝓞 E) (u.adicCompletion E) c ∈ u.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, val_alg]
  exact u.intValuation_le_one c

private theorem exS (w : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) :
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ u : HeightOneSpectrum (𝓞 E), u ≠ w →
      Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s) ≤ Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) c) := by
  classical
  have hI : Ideal.span {c} ≠ ⊥ := by simpa using hc
  have := w.isMaximal
  obtain ⟨Q, hQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hI w.asIdeal
  have hex : ∃ s ∈ Q, s ∉ w.asIdeal := by
    by_contra hcon
    push_neg at hcon
    have : Q ≤ w.asIdeal := hcon
    rw [sup_eq_left.2 this] at hQ
    exact w.isPrime.ne_top hQ
  obtain ⟨s, hsQ, hsw⟩ := hex
  refine ⟨s, hsw, fun u hu => ?_⟩
  rw [val_alg, val_alg]
  rw [HeightOneSpectrum.intValuation_if_neg u hc]
  refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u s _).2 ?_
  set e := (Associates.mk u.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hce : c ∈ u.asIdeal ^ e := by
    refine (HeightOneSpectrum.intValuation_le_pow_iff_mem u c e).1 ?_
    rw [HeightOneSpectrum.intValuation_if_neg u hc]
  have hle : Ideal.span {c} ≤ u.asIdeal ^ e := (Ideal.span_singleton_le_iff_mem _).2 hce
  generalize Multiset.count w.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {c})) = m at hIQ
  have hdvd : u.asIdeal ^ e ∣ w.asIdeal ^ m * Q := by
    rw [← hIQ]; exact Ideal.dvd_iff_le.2 hle
  have hcop : IsCoprime (u.asIdeal ^ e) (w.asIdeal ^ m) := by
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal (fun h => hu (HeightOneSpectrum.ext h))
  exact Ideal.le_of_dvd (hcop.dvd_of_dvd_mul_left hdvd) hsQ

private theorem conj_int [IsCMField E] {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (a h : GL (Fin n) (u.adicCompletion E)) (ha : a ∈ KGL u (n := n))
    (t : u.adicCompletion E) (ht : ∀ i k, (t • h.val) i k ∈ u.adicCompletionIntegers E) (i k : Fin n) :
    t * (a * h * a⁻¹).val i k ∈ u.adicCompletionIntegers E := by
  obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha
  have e : t * (a * h * a⁻¹).val i k = (a.val * (t • h.val) * (a⁻¹).val) i k := by
    simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ (h2 _ _)
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem (h1 _ _) (ht _ _)

private theorem diag_int {n : ℕ} (u : HeightOneSpectrum (𝓞 E)) (ϖ : u.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E u ϖ) (i : ℕ)
    (y : 𝓞 E) (hy : y ∈ u.asIdeal) (a b : Fin n) :
    (algebraMap (𝓞 E) (u.adicCompletion E) y •
      Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) a b ∈ u.adicCompletionIntegers E := by
  rw [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h1 h2
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, val_alg]
    have h3 : u.intValuation y ≤ Valued.v ϖ := by
      rw [hϖ]
      have := (HeightOneSpectrum.intValuation_le_pow_iff_mem u y 1).2 (by rwa [pow_one])
      exact this
    exact mul_inv_le_one_of_le₀ h3 zero_le'
  · rw [mul_one]; exact alg_int u y
  · rw [mul_zero]; exact zero_mem _

end UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling

open UpperTheory.Gal.Int.Geo.Pl.Tj.TorusKilling in
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tKill :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TKill := by
  intro hS hD hL E _ _ _ A n p _ S F x hx N w σ i hi g hg
  have hqp := σ.atp.prime
  have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hc : ((Ideal.absNorm w.asIdeal ^ i : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hN0)
  obtain ⟨s, hsw, hs⟩ := exS w _ hc
  refine ⟨s, hsw, fun y hy v hv => ?_⟩
  have key : ∀ (u : Plc E) (a b : Fin n), algebraMap (𝓞 E) (u.adicCompletion E) (s * y) * F.cmp u g⁻¹ a b ∈ u.adicCompletionIntegers E := by
    intro u a b
    by_cases hqu : ((σ.q : ℕ) : 𝓞 E) ∈ u.asIdeal
    · have ha := F.a_int u σ.q hqp σ.good hqu
      by_cases huw : u = w
      · subst huw
        obtain ⟨ϖ, hϖ, ht⟩ := hg.at_w
        have hϖ0 : ϖ ≠ 0 := by
          intro h0
          rw [Formalism.UG.IsUnifV, h0, map_zero] at hϖ
          exact WithZero.zero_ne_coe hϖ
        have hinv : (comp u g⁻¹).val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1 := by
          have h1 : (comp u g⁻¹).val * (comp u g).val = 1 := by
            rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
          have h2 : (comp u g).val * (Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ⁻¹ else 1) = 1 := by
            rw [ht, Matrix.diagonal_mul_diagonal]
            have hk : ∀ k : Fin n, (if (k : ℕ) < i then ϖ else 1) * (if (k : ℕ) < i then ϖ⁻¹ else 1) = (1 : u.adicCompletion E) := by
              intro k
              split_ifs
              · exact mul_inv_cancel₀ (G₀ := u.adicCompletion E) hϖ0
              · exact mul_one 1
            simp only [hk]
            exact Matrix.diagonal_one
          calc (comp u g⁻¹).val = (comp u g⁻¹).val * ((comp u g).val * _) := by rw [h2, Matrix.mul_one]
            _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        rw [map_mul, mul_assoc]
        refine mul_mem (alg_int u s) (conj_int u _ _ ha _ (fun a b => ?_) a b)
        rw [hinv]
        exact diag_int u ϖ hϖ i y hy a b
      · have h1 := conj_int u (F.a u) (comp u g⁻¹) ha ((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E) (hg.back u) a b
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
        rw [map_mul, map_mul, map_mul, mul_comm (Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) s)), mul_assoc]
        have h2 := hs u huw
        rw [map_natCast] at h2
        have h3 : Valued.v (algebraMap (𝓞 E) (u.adicCompletion E) y) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (alg_int u y)
        rw [map_mul] at h1
        calc _ ≤ 1 * (Valued.v (((Ideal.absNorm w.asIdeal ^ i : ℕ) : u.adicCompletion E)) * Valued.v (F.cmp u g⁻¹ a b)) :=
              mul_le_mul' h3 (mul_le_mul' h2 le_rfl)
          _ ≤ 1 := by rw [one_mul]; exact h1
    · have hne : u ≠ w := fun h => hqu (h ▸ hqw)
      have hoff : comp u g = 1 := hg.off u hne fun hK => hqu ?_
      · have h1 : F.cmp u g⁻¹ = 1 := by
          simp [Frame.cmp, map_inv, hoff]
        rw [h1, Matrix.one_apply]
        split_ifs
        · rw [mul_one]; exact alg_int u _
        · rw [mul_zero]; exact zero_mem _
      · have hq' : ((σ.q : ℕ) : 𝓞 E) ∈ (cj u).asIdeal := (hK _ (by simp)).2 hqw
        have e : (cj u).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
        rw [e, Ideal.mem_comap, map_natCast] at hq'
        exact hq'
  classical
  let Y : ∀ u : Plc E, Fin n → u.adicCompletion E := fun u =>
    if (p : 𝓞 E) ∈ u.asIdeal then 0 else algebraMap (𝓞 E) (u.adicCompletion E) (s * y) • (F.cmp u g⁻¹ *ᵥ F.vec u (v))
  have hY : ∀ u k, Y u k ∈ u.adicCompletionIntegers E := by
    intro u k
    by_cases hp : (p : 𝓞 E) ∈ u.asIdeal
    · simp only [Y, if_pos hp]; exact zero_mem _
    · simp only [Y, if_neg hp, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
      refine sum_mem fun l _ => ?_
      rw [← mul_assoc]
      exact mul_mem (key u k l) ((F.vec_hat v).1 hv u hp l)
  obtain ⟨v', hv'⟩ := F.vec_surj Y hY
  refine ⟨v', (F.vec_hat v').2 fun u hu k => ?_, ?_⟩
  · rw [hv' u hu]; exact hY u k
  · refine sub_eq_zero.1 (F.vec_inj _ fun u hu => ?_)
    have hmul : (F.a u * comp u g * (F.a u)⁻¹).val * F.cmp u g⁻¹ = 1 := by
      rw [Frame.cmp, ← Units.val_mul, map_inv]
      simp
    rw [map_sub, F.vec_act u hu, F.vec_mul u hu, hv' u hu]
    simp only [Y, if_neg hu]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, sub_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.ExistsUnit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem mem_cj_iff (q : ℕ) (w : Plc E) : (q : 𝓞 E) ∈ (cj w).asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal := by
  have e : (cj w).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [e, Ideal.mem_comap, map_natCast]

private theorem sameK_nat {x : E} {u w : Plc E} (h : SameK x u w) (q : ℕ) :
    (q : 𝓞 E) ∈ u.asIdeal ↔ (q : 𝓞 E) ∈ w.asIdeal :=
  h _ (by simpa using natCast_mem (IntermediateField.adjoin ℚ {x}) q)

private theorem intM_conj {u : Plc E} {a : GLw n u} (ha : a ∈ KGL u (n := n))
    {M : Matrix (Fin n) (Fin n) (u.adicCompletion E)} (hM : IntM u M) : IntM u (a.val * M * (a⁻¹).val) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 ha
  intro i k
  rw [Matrix.mul_apply]
  refine sum_mem fun l _ => mul_mem ?_ (h2 l k)
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem (h1 i m) (hM m l)

private theorem intM_one (u : Plc E) : IntM u (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  intro i k
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private def evQ (v : Plc ℚ) : AfQ →+* v.adicCompletion ℚ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem val_nat_ne (v : Plc ℚ) {c : ℕ} (hc : c ≠ 0) :
    Valued.v ((c : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [Ne, map_eq_zero]
  exact_mod_cast hc

private theorem exists_unit (s : AfQˣ) {c : ℕ} (hc : c ≠ 0)
    (hs : ∀ v : Plc ℚ, Valued.v ((s : AfQ) v) = Valued.v ((c : ℕ) : v.adicCompletion ℚ)) :
    ∃ u : AfQˣ, u ∈ UpperTheory.Gal.CertificateRingHomMap.ZU ∧ (s : AfQ) = (c : AfQ) * (u : AfQ) := by
  have hq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  let cu : AfQˣ := Units.map (algebraMap ℚ AfQ).toMonoidHom (Units.mk0 (c : ℚ) hq)
  have hcu : (cu : AfQ) = (c : AfQ) := by
    show algebraMap ℚ AfQ (c : ℚ) = _
    exact map_natCast _ c
  refine ⟨s * cu⁻¹, fun v => ?_, ?_⟩
  · have e : (s : AfQ) = ((s * cu⁻¹ : AfQˣ) : AfQ) * (c : AfQ) := by
      rw [← hcu, ← Units.val_mul, inv_mul_cancel_right]
    have e2 : (s : AfQ) v = ((s * cu⁻¹ : AfQˣ) : AfQ) v * ((c : ℕ) : v.adicCompletion ℚ) := by
      have := congrArg (evQ v) e
      rwa [map_mul, map_natCast] at this
    have h := hs v
    rw [e2, map_mul] at h
    exact mul_right_cancel₀ (val_nat_ne v hc) (h.trans (one_mul _).symm)
  · rw [← hcu, ← Units.val_mul, mul_comm cu, inv_mul_cancel_right]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.Int.Geo.Pl.Tj.tMult :
    UpperTheory.Gal.Int.Geo.Pl.Tj.TMult := by
  intro _ hDict _ E _ _ _ A n p _ S F x _ N w σ i _ g hs
  have hq : σ.q.Prime := σ.atp.prime
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
  have hoff : ∀ u : Plc E, (σ.q : 𝓞 E) ∉ u.asIdeal → comp u g = 1 := fun u hu =>
    hs.off u (by rintro rfl; exact hu hqw) fun hc => hu ((mem_cj_iff _ u).1 ((sameK_nat hc _).2 hqw))
  have hD := hDict E A n p S F g
  have hcmp : ∀ (u : Plc E) (h : GUf E n), F.cmp u h = (F.a u).val * (comp u h).val * ((F.a u)⁻¹).val := fun _ _ => rfl
  have hc0 : Ideal.absNorm w.asIdeal ^ i ≠ 0 := by
    have hb : w.asIdeal ≠ ⊥ := w.ne_bot
    exact pow_ne_zero _ (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  refine ⟨hD.1.2 fun u _ => ?_, ?_, (hD.2.2.2 _).2 fun u _ => ?_⟩
  · rw [hcmp]
    by_cases hu : (σ.q : 𝓞 E) ∈ u.asIdeal
    · exact intM_conj (F.a_int u σ.q hq σ.good hu) (hs.int u)
    · rw [hoff u hu, Units.val_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact intM_one u
  · obtain ⟨t, ht, e⟩ := exists_unit (sim g) hc0 hs.sim
    have hint : ∀ y ∈ UpperTheory.Gal.CertificateRingHomMap.ZU, IsIntAf (F.ρ (y : AfQ)) := fun y hy =>
      (F.ρ_int _).2 fun v _ => (hy v).le
    refine ⟨F.ρ t, F.ρ (t⁻¹ : AfQˣ), hint t ht, hint _ (inv_mem ht), ?_, ?_⟩
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [e, map_mul, map_natCast]
  · intro k l
    rw [hcmp]
    by_cases hu : (σ.q : 𝓞 E) ∈ u.asIdeal
    · have h := intM_conj (F.a_int u σ.q hq σ.good hu) (hs.back u) k l
      rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h
    · rw [map_inv, hoff u hu, inv_one, Units.val_one, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact mul_mem (natCast_mem _ _) (intM_one u k l)
end

