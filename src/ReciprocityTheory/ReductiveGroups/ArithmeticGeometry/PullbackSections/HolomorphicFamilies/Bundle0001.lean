module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.IdemDataBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamData
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

variable {E : Type} [Field E] [NumberField E]

abbrev nI (E : Type) [Field E] [NumberField E] : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))

def omF (i : Fin (nI E)) : 𝓞 E :=
  RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)

def omDF (i : Fin (nI E)) : E :=
  TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)

def bD (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) (i : Fin (nI E)) : 𝓞 E := ⟨_, hδ i⟩

def cD {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (i : Fin (nI E)) : k := ψ (omF i : E) / ψ (δ : E)

theorem omF_int_basis (i : Fin (nI E)) :
    integralBasis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) = (omF i : E) := by
  rw [NumberField.integralBasis_apply]
  rfl

theorem sum_omDF_omF : ∑ i, omDF (E := E) i * (omF i : E) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.sum_dual_mul (integralBasis E)
  rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [omF_int_basis]
  rfl

theorem ev_D {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i))
    (hψδ : ψ (δ : E) ≠ 0) : evD (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) = 1 := by
  unfold evD cD bD
  have e : ∀ i, ψ (omF (E := E) i : E) / ψ (δ : E) *
      (ψ.comp (algebraMap (𝓞 E) E)) ⟨(δ : E) * omDF i, hδ i⟩ = ψ (omDF i * omF i) := by
    intro i
    show ψ (omF (E := E) i : E) / ψ (δ : E) * ψ ((δ : E) * omDF i) = _
    rw [map_mul, map_mul]
    field_simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl fun i _ => e i, ← map_sum, sum_omDF_omF, map_one]

theorem dual_mul_expand (a : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * TB.trDual (integralBasis E) i =
      ∑ j, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E j) i : ℤ) : ℚ) • TB.trDual (integralBasis E) j := by
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand (integralBasis E) ((a : E) * TB.trDual (integralBasis E) i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hb : ∀ l, integralBasis E l = ((RingOfIntegers.basis E l : 𝓞 E) : E) :=
    fun l => NumberField.integralBasis_apply E l
  have e1 : (a : E) * TB.trDual (integralBasis E) i * integralBasis E j =
      TB.trDual (integralBasis E) i * ((a * RingOfIntegers.basis E j : 𝓞 E) : E) := by
    rw [hb]
    push_cast
    ring
  rw [e1, ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E j)]
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, ← hb,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_dual_mul]
  simp

theorem eqv_D {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) :
    IsEqv (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) := by
  intro a
  refine ⟨fun i j => (RingOfIntegers.basis E).repr
      (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
      ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i), fun i => ?_, fun j => ?_⟩
  · apply RingOfIntegers.ext
    have h1 := dual_mul_expand (E := E) a ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)
    rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h1
    show algebraMap (𝓞 E) E (a * bD δ hδ i) = algebraMap (𝓞 E) E (∑ j, _ • bD δ hδ j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum]
    show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) = _
    rw [show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) =
        (δ : E) * ((a : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) by ring, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    show (δ : E) * (_ • TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j)) =
      _ • ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
    simp only [zsmul_eq_mul, Rat.smul_def, Rat.cast_intCast]
    ring
  · simp only [cD, RingHom.comp_apply]
    have h2 : ((a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) :
        𝓞 E) : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : E) * (omF i : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))]
      rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm]
      push_cast
      simp [omF, zsmul_eq_mul]
    have h3 : ψ (a : E) * ψ (omF j : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr
        (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : k) * ψ (omF i : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, show (a : E) * (omF j : E) = ((a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) : 𝓞 E) : E) by simp [omF], h2, map_sum]
      simp [map_mul, map_intCast]
    rw [mul_div_assoc', h3, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem trace_int (x : 𝓞 E) : ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E (x : E) := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) (RingOfIntegers.isIntegral_coe x))
  exact ⟨z, by simpa using hz⟩

theorem one_eq_sum_trace : (1 : E) = ∑ i, Algebra.trace ℚ E (omF i : E) • omDF (E := E) i := by
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dual_expand (integralBasis E) (1 : E)
  rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [one_mul, omF_int_basis]
  rfl

theorem comp_D {k : Type} [Field k] [CharZero k] {Ty : Type} [Fintype Ty] (ψ : Ty → E →+* k)
    (htr : ∀ x : E, ∑ t, ψ t x = algebraMap ℚ k (Algebra.trace ℚ E x)) (N : ℕ) (hN : N ≠ 0)
    (hδ : ∀ i, IsIntegral ℤ (((N : 𝓞 E) : E) * omDF (E := E) i)) {d : ℕ} (M : 𝓞 E →+* Matrix (Fin d) (Fin d) k) :
    ∑ t, actD M (bD (N : 𝓞 E) hδ) (cD (ψ t) (N : 𝓞 E)) = 1 := by
  classical
  choose z hz using fun i : Fin (nI E) => trace_int (E := E) (omF i)
  have hN' : (N : k) ≠ 0 := Nat.cast_ne_zero.2 hN

  have hsum : ∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i = (N : 𝓞 E) := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) = algebraMap (𝓞 E) E (N : 𝓞 E)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_natCast]
    have h1 := one_eq_sum_trace (E := E)
    have e : ∀ i, algebraMap (𝓞 E) E ((z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) =
        (N : E) * (Algebra.trace ℚ E (omF i : E) • omDF (E := E) i) := by
      intro i
      rw [map_mul, map_intCast, ← hz i, Rat.smul_def, Rat.cast_intCast]
      show (z i : E) * (((N : 𝓞 E) : E) * omDF (E := E) i) = _
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, ← h1, mul_one]
  have hM : ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) = (N : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    have := congrArg M hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_natCast] at this
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, ← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have htr : ∀ i, ∑ t, ψ t (omF i : E) = (z i : k) := by
    intro i
    rw [htr, ← hz i]
    simp
  unfold actD cD
  rw [Finset.sum_comm]
  calc ∑ i, ∑ t, (ψ t (omF i : E) / ψ t ((N : 𝓞 E) : E)) • M (bD (N : 𝓞 E) hδ i)
      = ∑ i, ((N : k)⁻¹ * (z i : k)) • M (bD (N : 𝓞 E) hδ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [map_natCast, div_eq_mul_inv]
        rw [← Finset.sum_mul, htr, mul_comm]
    _ = (N : k)⁻¹ • ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) := by
        rw [Finset.smul_sum]
        simp [mul_smul]
    _ = 1 := by rw [hM, smul_smul, inv_mul_cancel₀ hN', one_smul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamLift
section
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [Field k] [Algebra ℚ k] [Algebra R k]

theorem actP_eq_sum (B : FB R d O) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (ξ : (Fin d → k) × (Fin d → k)) :
    actP B b c ξ = ∑ i, c i • OactH k B (b i) ξ := by
  unfold actP actD
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    rfl
  · rw [Prod.snd_sum]
    rfl

theorem actP_mem (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) {n : ℕ}
    (b : Fin n → O) (a : Fin n → R) {ξ : (Fin d → k) × (Fin d → k)} (hξ : ξ ∈ Hset (R := R) k h) :
    actP B b (fun i => algebraMap R k (a i)) ξ ∈ Hset (R := R) k h := by
  rw [actP_eq_sum]
  have hmem : ∀ i, OactH k B (b i) ξ ∈ Hset (R := R) k h := fun i =>
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gauge_stable R d O k hRQ B h hc (b i) ξ hξ
  choose u φ hu using hmem
  refine ⟨∑ i, a i • u i, ∑ i, a i • φ i, ?_⟩
  have hvec : (fun j => algebraMap R k ((∑ i, a i • u i) j)) =
      ∑ i, algebraMap R k (a i) • fun j => algebraMap R k (u i j) := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Algebra.smul_def]
  simp_rw [hu]
  refine Prod.ext ?_ ?_
  · funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Prod.fst_sum, Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Algebra.smul_def]
  · rw [hvec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Prod.snd_sum, Finset.sum_apply, map_sum, map_mul, smul_eq_mul, Matrix.mulVec_smul, mul_sub,
      Finset.sum_sub_distrib, Algebra.smul_def]

theorem actP_smul (B : FB R d O) {n : ℕ} (b : Fin n → O) (c : Fin n → k) (r : k) (ξ : (Fin d → k) × (Fin d → k)) :
    r • actP B b c ξ = actP B b (fun i => r * c i) ξ := by
  unfold actP actD
  simp only [Prod.smul_mk, ← Matrix.smul_mulVec, Finset.smul_sum, smul_smul]

theorem actP_fst_eig (B : FB R d O) (χ : O →+* k) {n : ℕ} (b : Fin n → O) (c : Fin n → k)
    (ξ : (Fin d → k) × (Fin d → k)) (hv : ∀ a, (dAct k B a).mulVec ξ.1 = χ a • ξ.1) :
    (actP B b c ξ).1 = evD χ b c • ξ.1 := by
  unfold actP actD evD
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show c i • (dAct k B (b i)).mulVec ξ.1 = _
  rw [hv, smul_smul]

theorem hset_snd_int {h : PS k 2 d} {X : Fin d → k} (hX : ((0 : Fin d → k), X) ∈ Hset (R := R) k h) (_hinj : Function.Injective (algebraMap R k)) :
    ∀ i, X i ∈ (algebraMap R k).range := by
  intro i
  obtain ⟨u, φ, hξ⟩ := hX
  have h1 := congrArg Prod.fst hξ
  have h2 := congrArg Prod.snd hξ
  simp only at h1 h2
  rw [← h1, Matrix.mulVec_zero] at h2
  simp only [Pi.zero_apply, sub_zero] at h2
  exact ⟨φ i, (congrFun h2 i).symm⟩

theorem betaH_sub_left (ξ ξ' η : (Fin d → k) × (Fin d → k)) : betaH k (ξ - ξ') η = betaH k ξ η - betaH k ξ' η := by
  unfold betaH
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  ring

theorem betaH_sub_right (ξ η η' : (Fin d → k) × (Fin d → k)) : betaH k ξ (η - η') = betaH k ξ η - betaH k ξ η' := by
  unfold betaH
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  ring


open Classical in
theorem eigLiftRam_core (hRQ : IsRQ (R := R) k) (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h)
    {L Ty Pl π : Type} [Fintype Ty] (ty : L → Ty) (χ : Ty → O →+* k) (cjT : Ty → Ty)
    (hχsep : ∀ t t', t' ≠ cjT t → ∃ a, χ t a ≠ χ t' (star a)) (hχinj : ∀ t t', t ≠ t' → ∃ a, χ t a ≠ χ t' a)
    (u : L → Fin d → R)
    (heig : ∀ ℓ a, (dAct k B a).mulVec (fun i => algebraMap R k (u ℓ i)) = χ (ty ℓ) a • fun i => algebraMap R k (u ℓ i))
    (nt : Ty → ℕ) (bt : ∀ t, Fin (nt t) → O) (ct : ∀ t, Fin (nt t) → k) (heqt : ∀ t, IsEqv (χ t) (bt t) (ct t))
    (hcompH : ∑ t, actD (EigA.dActH k B) (bt t) (ct t) = 1) (hcompS : ∑ t, actD (EigA.dActS k B) (bt t) (ct t) = 1)
    (pl : Ty → Pl) (cjP : Pl → Pl) (hpl : ∀ t, pl (cjT t) = cjP (pl t))
    (nP : Pl → ℕ) (bP : ∀ w, Fin (nP w) → O) (aP : ∀ w, Fin (nP w) → R)
    (hP : ∀ w t, evD (χ t) (bP w) (fun i => algebraMap R k (aP w i)) = if pl t = w then 1 else 0)
    (nE : Ty → ℕ) (bE : ∀ t, Fin (nE t) → O) (cE : ∀ t, Fin (nE t) → k) (heqE : ∀ t, IsEqv (χ t) (bE t) (cE t))
    (hnE : ∀ t, evD (χ t) (bE t) (cE t) = 1) (r : Ty → R)
    (hr : ∀ t i, ∃ v : R, algebraMap R k v = algebraMap R k (r t) * cE t i)
    (c : Ty → π) (s : Ty → Bool) (hpair : ∀ t t', pl t' = cjP (pl t) → c t = c t' ∧ s t ≠ s t') :
    ∃ (φ : L → Fin d → R) (ψ : L → Fin d → k),
      (∀ ℓ i, algebraMap R k (r (ty ℓ)) * ψ ℓ i ∈ (algebraMap R k).range) ∧
      (∀ ℓ ℓ', ty ℓ' ≠ cjT (ty ℓ) →
        ∑ i, (algebraMap R k (φ ℓ' i) + ψ ℓ' i - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
          algebraMap R k (u ℓ i) = 0) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ)) (fun ℓ => (0, ψ ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i)) ∧
      OppositePairVanishing k (fun ℓ => c (ty ℓ)) (fun ℓ => s (ty ℓ))
        (fun ℓ => ((fun j => algebraMap R k (u ℓ j)),
          fun i => algebraMap R k (φ ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i))
        (fun ℓ => (0, ψ ℓ)) := by
  classical
  have hinj : Function.Injective (algebraMap R k) := hRQ.1

  have hξ0 : ∀ ℓ, ((fun j => algebraMap R k (u ℓ j)), -(sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j))) ∈
      Hset (R := R) k h := fun ℓ => ⟨u ℓ, 0, Prod.ext rfl (by funext i; simp)⟩
  let ξh : L → (Fin d → k) × (Fin d → k) := fun ℓ => actP B (bP (pl (ty ℓ))) (fun i => algebraMap R k (aP (pl (ty ℓ)) i))
    ((fun j => algebraMap R k (u ℓ j)), -(sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)))
  have hξh_mem : ∀ ℓ, ξh ℓ ∈ Hset (R := R) k h := fun ℓ => actP_mem hRQ B h hc _ _ (hξ0 ℓ)
  have hξh_fst : ∀ ℓ, (ξh ℓ).1 = fun j => algebraMap R k (u ℓ j) := by
    intro ℓ
    show (actP B _ _ _).1 = _
    rw [actP_fst_eig B (χ (ty ℓ)) _ _ _ (heig ℓ), hP, if_pos rfl, one_smul]
  choose u1 φ1 hu1 using hξh_mem
  have hU1 : ∀ ℓ, (fun j => algebraMap R k (u1 ℓ j)) = fun j => algebraMap R k (u ℓ j) := fun ℓ =>
    (congrArg Prod.fst (hu1 ℓ)).symm.trans (hξh_fst ℓ)
  have hξh_eq : ∀ ℓ, ξh ℓ = ((fun j => algebraMap R k (u ℓ j)),
      fun i => algebraMap R k (φ1 ℓ i) - (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ j)) i) := by
    intro ℓ
    rw [hu1 ℓ, hU1 ℓ]

  let ξ : L → (Fin d → k) × (Fin d → k) := fun ℓ => actP B (bE (ty ℓ)) (cE (ty ℓ)) (ξh ℓ)
  have heigh : ∀ ℓ a, (dAct k B a).mulVec (ξh ℓ).1 = χ (ty ℓ) a • (ξh ℓ).1 := fun ℓ a => by
    rw [hξh_fst]; exact heig ℓ a
  have hξ_fst : ∀ ℓ, (ξ ℓ).1 = fun j => algebraMap R k (u ℓ j) := by
    intro ℓ
    show (actP B _ _ _).1 = _
    rw [actP_fst_eig B (χ (ty ℓ)) _ _ _ (heigh ℓ), hnE, one_smul, hξh_fst]
  let ψ : L → Fin d → k := fun ℓ i => (ξ ℓ).2 i - (ξh ℓ).2 i
  have hdiff : ∀ ℓ, ξ ℓ - ξh ℓ = ((0 : Fin d → k), ψ ℓ) := by
    intro ℓ
    refine Prod.ext ?_ rfl
    rw [Prod.fst_sub, hξ_fst, hξh_fst, sub_self]

  have hsuppP : ∀ w t, evD (χ t) (bP w) (fun i => algebraMap R k (aP w i)) ≠ 0 → pl t = w := by
    intro w t ht
    rw [hP] at ht
    by_contra hne
    exact ht (if_neg hne)
  have hsuppE : ∀ τ t, evD (χ t) (bE τ) (cE τ) ≠ 0 → pl t = pl τ := by
    intro τ t ht
    by_cases he : t = τ
    · rw [he]
    · obtain ⟨a, ha⟩ := hχinj t τ he
      exact absurd (evD_orth (χ τ) (χ t) (bE τ) (cE τ) (heqE τ) a ha) ht
  have hvan : ∀ {n n' : ℕ} (bz : Fin n → O) (cz : Fin n → k) (bw : Fin n' → O) (cw : Fin n' → k)
      (X Y : (Fin d → k) × (Fin d → k)) (l l' : L), ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) →
      (∀ t, evD (χ t) bz cz ≠ 0 → pl t = pl (ty l)) → (∀ t', evD (χ t') bw cw ≠ 0 → pl t' = pl (ty l')) →
      betaH k (actP B bz cz X) (actP B bw cw Y) = 0 := by
    intro n n' bz cz bw cw X Y l l' hnot hs1 hs2
    refine beta_vanish B χ nt bt ct heqt hcompH hcompS bz cz bw cw X Y fun t t' h1 h2 => ?_
    by_cases ht : t' = cjT t
    · exfalso
      apply hnot
      apply hpair
      rw [← hs2 t' h2, ht, hpl, hs1 t h1]
    · exact hχsep t t' ht
  have hA : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξh l) (ξh l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppP _) (hsuppP _)
  have hB : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξ l) (ξh l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppE _) (hsuppP _)
  have hC : ∀ l l', ¬ (c (ty l) = c (ty l') ∧ s (ty l) ≠ s (ty l')) → betaH k (ξh l) (ξ l') = 0 :=
    fun l l' hnot => hvan _ _ _ _ _ _ l l' hnot (hsuppP _) (hsuppE _)
  refine ⟨φ1, ψ, fun ℓ i => ?_, fun ℓ ℓ' hne => ?_, fun l l' hnot => ?_, fun l l' hnot => ?_, fun l l' hnot => ?_⟩
  ·
    choose v hv using hr (ty ℓ)
    have hrξ : algebraMap R k (r (ty ℓ)) • ξ ℓ ∈ Hset (R := R) k h := by
      show algebraMap R k (r (ty ℓ)) • actP B _ _ _ ∈ _
      rw [actP_smul]
      have e : (fun i => algebraMap R k (r (ty ℓ)) * cE (ty ℓ) i) = fun i => algebraMap R k (v i) :=
        funext fun i => (hv i).symm
      rw [e]
      exact actP_mem hRQ B h hc _ _ (hu1 ℓ ▸ ⟨u1 ℓ, φ1 ℓ, rfl⟩)
    have hrξh : algebraMap R k (-1) • (algebraMap R k (r (ty ℓ)) • ξh ℓ) ∈ Hset (R := R) k h :=
      EigA.hset_smul k h (-1) (EigA.hset_smul k h (r (ty ℓ)) (hu1 ℓ ▸ ⟨u1 ℓ, φ1 ℓ, rfl⟩))
    have hsum := EigA.hset_add k h hrξ hrξh
    have e2 : algebraMap R k (r (ty ℓ)) • ξ ℓ + algebraMap R k (-1) • (algebraMap R k (r (ty ℓ)) • ξh ℓ) =
        ((0 : Fin d → k), fun i => algebraMap R k (r (ty ℓ)) * ψ ℓ i) := by
      rw [map_neg, map_one, neg_one_smul, ← sub_eq_add_neg, ← smul_sub, hdiff]
      refine Prod.ext ?_ ?_
      · simp
      · funext i
        simp [Algebra.smul_def]
    rw [e2] at hsum
    exact hset_snd_int hsum hinj i
  ·
    obtain ⟨a, ha⟩ := hχsep (ty ℓ) (ty ℓ') hne
    have hv1 : ∀ b : O, OactH k B b ((fun j => algebraMap R k (u ℓ j)), (0 : Fin d → k)) =
        χ (ty ℓ) b • ((fun j => algebraMap R k (u ℓ j)), (0 : Fin d → k)) := by
      intro b
      rw [EigA.OactH_eq]
      refine Prod.ext (heig ℓ b) ?_
      simp
    have hβ := eigen_orthogonality R d O k B (χ (ty ℓ)) (χ (ty ℓ')) _ (ξ ℓ') hv1
      (fun b => actP_eig B (χ (ty ℓ')) _ _ (heqE (ty ℓ')) (ξh ℓ') b)
      ⟨a, isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)⟩
    simp only [betaH, Pi.zero_apply, zero_mul, sub_zero] at hβ
    have e3 : ∀ i, (ξ ℓ').2 i = algebraMap R k (φ1 ℓ' i) + ψ ℓ' i -
        (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i := by
      intro i
      show (ξ ℓ').2 i = algebraMap R k (φ1 ℓ' i) + ((ξ ℓ').2 i - (ξh ℓ').2 i) -
        (sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i
      rw [hξh_eq ℓ']
      ring
    simp only [e3] at hβ
    exact hβ
  · dsimp only
    rw [← hξh_eq l, ← hξh_eq l']
    exact hA l l' hnot
  · dsimp only
    rw [← hξh_eq l', ← hdiff l, betaH_sub_left, hB l l' hnot, hA l l' hnot, sub_zero]
  · dsimp only
    rw [← hξh_eq l, ← hdiff l', betaH_sub_right, hC l l' hnot, hA l l' hnot, sub_zero]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SingleMemDegLE
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

section Alg

variable {V : Type} [CommRing V]

theorem aeval_tan {ι : Type} [DecidableEq ι] (ℓ : ι) (P : MvPolynomial ι V) :
    aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) P =
      algebraMap V (DualNumber V) (constantCoeff P) + AddMonoidAlgebra.coeff P (Finsupp.single ℓ 1) • DualNumber.eps := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C, MvPolynomial.coeff_C,
      if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq => rw [map_add (f := _), hp, hq, map_add (f := _), map_add (f := _), MvPolynomial.coeff_add, add_smul]; abel
  | mul_X p n hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add,
      MvPolynomial.coeff_mul_X']
    by_cases h : n = ℓ
    · subst h
      have hs : n ∈ (Finsupp.single n (1 : ℕ)).support := by simp
      rw [if_pos rfl, if_pos hs, tsub_self, ← MvPolynomial.constantCoeff_eq, add_mul, smul_mul_assoc,
        DualNumber.eps_mul_eps, smul_zero, add_zero, Algebra.smul_def]
    · have : n ∉ (Finsupp.single ℓ 1).support := by simp [Finsupp.support_single_ne_zero, Ne.symm h, h]
      simp [h, this]

theorem coeff_psTrunc {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι V) (e : ι →₀ ℕ)
    (he : e ∈ degLE m) : AddMonoidAlgebra.coeff (psTrunc m f) e = MvPowerSeries.coeff e f := by
  simp [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he]

theorem single_mem_degLE {ι : Type} [Fintype ι] [DecidableEq ι] (ℓ : ι) : Finsupp.single ℓ 1 ∈ degLE (ι := ι) 1 := by
  simp only [degLE, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨fun i => if i = ℓ then 1 else 0, ?_⟩, ?_⟩
  · ext i
    by_cases h : i = ℓ
    · subst h; simp
    · simp [h, Finsupp.single_apply, Ne.symm h]
  · simp [Finsupp.sum_single_index]

theorem ker_jetAug_sq {κ : Type} : (RingHom.ker (jetAug (R := V) (ι := κ) (m := 1))) ^ (1 + 1) = ⊥ := by
  exact ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow κ 1

end Alg

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

