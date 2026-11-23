module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorLatticeScaling
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem monomial_exponent_le_multidegree {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (l : ι) (a : Fin n) : m (l, a) ≤ multideg m l := by
  exact Finset.single_le_sum (f := fun c => m (l, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem polynomial_weight_difference_le {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (d : ι → ℕ)
    (m m' : ι × Fin n →₀ ℕ) (hm : ∀ i, multideg m i = d i) (hm' : ∀ i, multideg m' i = d i) (a b : Fin n) :
    wtS LL S m a - wtS LL S m' b ≤ (degIn d S : ℤ) := by
  unfold wtS degIn
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := monomial_exponent_le_multidegree m l a
  have h2 := monomial_exponent_le_multidegree m' l b
  rw [hm l] at h1
  rw [hm' l] at h2
  split_ifs <;> omega

theorem prime_pow_smul_cast {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p k : ℕ) (y : MvPolynomial σ (KK O)) :
    ((p : O) ^ k) • y = ((p : KK O) ^ k) • y := by
  rw [← algebraMap_smul (KK O) ((p : O) ^ k) y, map_pow, map_natCast]

theorem isotypic_projector_lattice_scaling (D : Formalism.BasicNotions.D7) (hDom : HighestWeightDominant) (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (h13 : IsotypicProjectorTheoremField D)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) [CharZero (KK O)] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (lam : Fin n → ℤ) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)))
    (he : IsIsoProj (glOps (KK O) n LL S) lam e) :
    (∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d) ∧
    ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
      (∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
      MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ →
      ∀ F ∈ Pol (KK O) n d, F ∈ L →
        ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • e F ∈ L := by
  obtain ⟨hRep, -, -, hStab, hFD, hWt, -⟩ := hPol (KK O) ι n LL
  have hStabS : ∀ a b, ∀ x ∈ Pol (KK O) n d, glOps (KK O) n LL S a b x ∈ Pol (KK O) n d :=
    fun a b x hx => hStab S d a b x hx
  obtain ⟨hResRep, hResWt, hResDiv, hResBin, hResProj, hResZero⟩ :=
    hRes (KK O) (MvPolynomial (ι × Fin n) (KK O)) n (glOps (KK O) n LL S) (hRep S) (Pol (KK O) n d) hStabS
  obtain ⟨e', he'P, he'eq⟩ := hResProj lam e he
  have hPres : ∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d := by
    intro F hF
    have h := (e' ⟨F, hF⟩).2
    rwa [he'eq ⟨F, hF⟩] at h
  refine ⟨hPres, ?_⟩
  intro L hLst hFG hMQ F hF hFL
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hid : e F = F := by
      by_cases h0 : F = 0
      · rw [h0, map_zero]
      · apply he.1
        apply Submodule.subset_span
        refine ⟨1, Submonoid.one_mem _, F, ⟨h0, ?_, fun a => a.elim0⟩, by simp⟩
        simp [weightSp]
    rw [hid]
    simpa [N0] using hFL
  · have : NeZero n := ⟨hn.ne'⟩
    have : FiniteDimensional (KK O) (Pol (KK O) n d) := hFD d

    have hwt : ∀ (mu : Fin n → ℤ) (x : Pol (KK O) n d), x ≠ 0 →
        x ∈ weightSp (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) mu →
        ∃ m : ι × Fin n →₀ ℕ, (∀ i, multideg m i = d i) ∧ wtS LL S m = mu := by
      intro mu x hx0 hx
      have hxV := (hResWt mu x).mp hx
      have hne : (x : MvPolynomial (ι × Fin n) (KK O)) ≠ 0 := by simpa using hx0
      obtain ⟨m, hm⟩ : (x : MvPolynomial (ι × Fin n) (KK O)).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
      refine ⟨m, ?_, hWt S mu _ hxV m hm⟩
      have hx2 : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := x.2
      exact (show ((x : MvPolynomial (ι × Fin n) (KK O)).support : Set (ι × Fin n →₀ ℕ)) ⊆
        {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} from hx2) hm
    by_cases hhw : ∃ v : Pol (KK O) n d,
        IsHWV (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) lam v
    · have hdom : Dominant lam := by
        obtain ⟨v, hv⟩ := hhw
        exact hDom (KK O) (Pol (KK O) n d) n _ hResRep lam v hv
      have hWtBound : ellWt lam ≤ degIn d S := by
        obtain ⟨v, hv⟩ := hhw
        obtain ⟨m, hmd, hmw⟩ := hwt lam v hv.1 hv.2.1
        have h := polynomial_weight_difference_le LL S d m m hmd hmd 0 (lastIdx n)
        rw [hmw] at h
        unfold ellWt
        omega
      have hEllBound : ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ ≤ degIn d S := by
        unfold ellOf
        apply csSup_le'
        rintro k ⟨mu, hmu, nu, hnu, a, b, hab, hk⟩
        obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hmu)
        obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hnu)
        obtain ⟨m, hmd, hmw⟩ := hwt mu x hx0 hx
        obtain ⟨m', hmd', hmw'⟩ := hwt nu y hy0 hy
        have e1 := congrFun hk a
        have e2 := congrFun hk b
        simp [rootW, hab, Ne.symm hab] at e1 e2
        have d1 := polynomial_weight_difference_le LL S d m m hmd hmd a b
        have d2 := polynomial_weight_difference_le LL S d m' m' hmd' hmd' b a
        rw [hmw] at d1
        rw [hmw'] at d2
        omega
      have hLat : UZLattice (O := O) (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS)
          (latticeMultidegreePart L d) := by
        refine ⟨?_, hFG⟩
        intro u hu x hx
        rw [latticeMultidegreePart, Submodule.mem_comap] at hx ⊢
        rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
        · change ((divPowE _ a b k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResDiv a b k x]
          exact hLst _ (Or.inl ⟨a, b, k, hab, rfl⟩) _ hx
        · change ((binomE _ a k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResBin a k x]
          exact hLst _ (Or.inr ⟨a, k, rfl⟩) _ hx
      have key := h13 p n' O S0 hG n (Pol (KK O) n d) _ hResRep (latticeMultidegreePart L d) hLat hMQ {lam}
        (by simpa using hdom) (fun _ => e') (by simpa using he'P) ⟨F, hF⟩ hFL
      simp only [Finset.sup_singleton, Finset.sum_singleton, hMQ] at key
      rw [latticeMultidegreePart, Submodule.mem_comap] at key
      have key' : ((p : O) ^ (N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤
          + ellWt lam))) • e F ∈ L := by
        simpa [he'eq] using key
      have hle : N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ + ellWt lam)
          ≤ N0 n * Nat.log p (2 * degIn d S + n - 1) := by
        unfold deF
        exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, ← prime_pow_smul_cast p _ (e F), pow_add, mul_comm, mul_smul]
      exact L.smul_mem _ key'
    · have h0 : e F = 0 := hResZero lam e he hhw F hF
      rw [h0, smul_zero]
      exact L.zero_mem

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repExistsHwv
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_comp_mem [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (s : Finset (Fin n → ℤ)) : ∀ g : (Fin n → ℤ) → V, (∀ ν ∈ s, g ν ∈ weightSp E ν) → ∑ ν ∈ s, g ν ∈ Z →
      ∀ ν ∈ s, g ν ∈ Z := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg hsum μ hμ
  by_cases hs : ∃ ν ∈ s, ν ≠ μ
  · obtain ⟨ν, hν, hne⟩ := hs
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
      by_contra h
      push_neg at h
      exact hne (funext h).symm
    let g' : (Fin n → ℤ) → V := fun ρ => (((ρ a - ν a : ℤ) : K)) • g ρ
    have hZ' : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) ∈ Z := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact Z.sub_mem (hZ a _ hsum) (Z.smul_mem _ hsum)
    have heq : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) = ∑ ρ ∈ s.erase ν, g' ρ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_erase_add _ _ hν]
      have h0 : (E a a - (ν a : K) • (1 : Module.End K V)) (g ν) = 0 := by
        have := (v2rep_mem_weightSp E ν (g ν)).mp (hg ν hν) a
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_self]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have := (v2rep_mem_weightSp E ρ (g ρ)).mp (hg ρ (Finset.mem_of_mem_erase hρ)) a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, ← sub_smul]
      simp only [g', Int.cast_sub]
    have hg' : ∀ ρ ∈ s.erase ν, g' ρ ∈ weightSp E ρ := fun ρ hρ =>
      (weightSp E ρ).smul_mem _ (hg ρ (Finset.mem_of_mem_erase hρ))
    have hIH := ih (s.erase ν) (Finset.erase_ssubset hν) g' hg' (heq ▸ hZ') μ
      (Finset.mem_erase.mpr ⟨hne.symm, hμ⟩)
    have hc : (((μ a - ν a : ℤ)) : K) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha
    have := Z.smul_mem (((μ a - ν a : ℤ) : K))⁻¹ hIH
    simp only [g'] at this
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push_neg at hs
    have : ∑ ν ∈ s, g ν = g μ :=
      Finset.sum_eq_single_of_mem μ hμ (fun ν hν hne => absurd (hs ν hν) hne)
    rw [this] at hsum
    exact hsum

theorem v2rep_graded [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (x : V) (hx : x ∈ Z) (hw : x ∈ ⨆ ν, weightSp E ν) : x ∈ ⨆ ν, weightSp E ν ⊓ Z := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hw
  have hsum : ∑ ν ∈ f.support, f ν ∈ Z := by simpa [Finsupp.sum] using hx
  have key := v2rep_comp_mem E Z hZ f.support f (fun ν _ => hf ν) hsum
  show ∑ ν ∈ f.support, f ν ∈ _
  exact Submodule.sum_mem _ fun ν hν => Submodule.mem_iSup_of_mem ν ⟨hf ν, key ν hν⟩

def weightHeight' (ν : Fin n → ℤ) : ℤ := -∑ a : Fin n, (a.val : ℤ) * ν a

theorem v2rep_ht_root (ν : Fin n → ℤ) (a b : Fin n) (h : a < b) : weightHeight' ν < weightHeight' (ν + rootW a b) := by
  have hab : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast h
  simp only [weightHeight', rootW, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

def heightOperator' (E : GLOps n K V) : Module.End K V := -∑ a : Fin n, ((a.val : ℤ) : K) • E a a

theorem v2rep_H_apply (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    heightOperator' E x = ((weightHeight' ν : ℤ) : K) • x := by
  rw [v2rep_mem_weightSp] at hx
  have h1 : heightOperator' E x = -∑ a : Fin n, (((a.val : ℤ) : K) * (ν a : K)) • x := by
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      hx, smul_smul]
  rw [h1, ← Finset.sum_smul, ← neg_smul]
  congr 1
  simp only [weightHeight']
  push_cast
  rfl

theorem v2rep_exists_hwv [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V)
    [FiniteDimensional K Z] (hZ : IsStableUnderOperators E Z) (hw : Z ≤ ⨆ ν, weightSp E ν) (hne : Z ≠ ⊥) :
    ∃ mu v, v ∈ Z ∧ IsHWV E mu v := by
  have hHZ : ∀ x ∈ Z, heightOperator' E x ∈ Z := by
    intro x hx
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Z.neg_mem (Z.sum_mem fun a _ => Z.smul_mem _ (hZ a a x hx))
  let HZ : Module.End K Z := (heightOperator' E).restrict hHZ
  let S : Set ℤ := {h | ∃ ν v, v ∈ Z ∧ v ≠ 0 ∧ v ∈ weightSp E ν ∧ weightHeight' ν = h}
  have hSeig : ∀ h ∈ S, HZ.HasEigenvalue (h : K) := by
    rintro h ⟨ν, v, hvZ, hv0, hvw, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvZ⟩) ?_
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_), fun h0 => hv0 (congrArg Subtype.val h0)⟩
    exact v2rep_H_apply E ν v hvw
  have hSfin : S.Finite :=
    ((Module.End.finite_hasEigenvalue HZ).preimage (Int.cast_injective (α := K)).injOn).subset
      fun h hh => hSeig h hh
  obtain ⟨x, hxZ, hx0⟩ := (Submodule.ne_bot_iff Z).mp hne
  have hgr := v2rep_graded E Z (fun a x hx => hZ a a x hx) x hxZ (hw hxZ)
  obtain ⟨ν0, hν0⟩ : ∃ ν, weightSp E ν ⊓ Z ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    simp [hc] at hgr
    exact hx0 hgr
  obtain ⟨v0, hv0m, hv00⟩ := (Submodule.ne_bot_iff _).mp hν0
  have hSne : S.Nonempty := ⟨_, ν0, v0, hv0m.2, hv00, hv0m.1, rfl⟩
  have hTne : hSfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hSfin).mpr hSne
  obtain ⟨ν, v, hvZ, hv0, hvw, hht⟩ := (hSfin.mem_toFinset).mp (hSfin.toFinset.max'_mem hTne)
  refine ⟨ν, v, hvZ, hv0, hvw, fun a b hab => ?_⟩
  by_contra hne'
  have hmem : weightHeight' (ν + rootW a b) ∈ S :=
    ⟨ν + rootW a b, E a b v, hZ a b v hvZ, hne', v2rep_shift E hR a b ν v hvw, rfl⟩
  have h1 := hSfin.toFinset.le_max' _ ((hSfin.mem_toFinset).mpr hmem)
  have h2 := v2rep_ht_root ν a b hab
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem sDegs_eq_support_mul_Phi_twistSub {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (j : Fin n) (H : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j H = (mul_Phi _ _ (twistSub LL S j H)).coeff.support := by
  ext k
  simp only [sDegs, Finset.mem_biUnion, Finsupp.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · rintro ⟨m, -, hk⟩ h0
    apply hk
    rw [← mul_Phi_coeff, h0, MvPolynomial.coeff_zero]
    rfl
  · intro hk
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [mul_Phi_coeff] at hm
    refine ⟨m, fun h => hm ?_, hm⟩
    rw [h]
    rfl

theorem mul_valS_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
  rw [valS, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_lam1S_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
  rw [lam1S, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  rw [mul_valS_eq LL S F, mul_valS_eq LL S G, mul_valS_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans ?_ (Finset.inf_mono Finsupp.support_add)
  rw [Finset.inf_union]
  exact le_rfl

theorem mul_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  rw [mul_lam1S_eq LL S F, mul_lam1S_eq LL S G, mul_lam1S_eq LL S (F + G), map_add (f := _), map_add (f := _)]
  refine le_trans (Finset.sup_mono Finsupp.support_add) ?_
  rw [Finset.sup_union]
  exact le_rfl

theorem valuation_bound_det_power_factor (R : Type) [Field R] (ι : Type) (LL : Letters ι) (r : ℕ) [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true)
    (G H : MvPolynomial (ι × Fin r) R) (m : ℕ) (hG : G = (detA (R := R) A) ^ m * H) (S' : Set ι) :
    valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ) := by
  have hd := mul_valS_detA_le (R := R) LL A hA hv S'
  have hpow : ∀ k : ℕ, valS LL S' ((detA (R := R) A) ^ (k + 1)) ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [pow_succ, mul_valS_mul]
      calc valS LL S' ((detA (R := R) A) ^ (k + 1)) + valS LL S' (detA (R := R) A)
          ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := add_le_add ih hd
        _ = (((k + 1 + 1 : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
  subst hG
  rcases m with _ | k
  · simp
  · rw [mul_valS_mul, add_comm (valS LL S' _) (valS LL S' H)]
    exact add_le_add (le_refl _) (hpow k)

def GlOperatorsFormRepresentation : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (h : GlOperatorsFormRepresentation) : ConclusionE D := by
  intro R _ ι _ LL r _ S A hA hAS
  exact ⟨h R ι LL r S A hA hAS,
    fun G H m hG S' => valuation_bound_det_power_factor R ι LL r A hA (fun l => (hAS l).2) G H m hG S'⟩

def GeneratedModuleWeightDescription : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι),
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ), ((th : WithTop ℤ) ≤ valS LL S G ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), th ≤ mu (lastIdx n))) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ), (lam1S LL S G ≤ (M : WithBot ℤ) ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), mu 0 ≤ M))

theorem valuations_additive_of_generated_weight_description (D : Formalism.BasicNotions.D7) (h : GeneratedModuleWeightDescription) : ValuationsAdditive D := by
  intro R _ ι _ LL n _ S
  exact ⟨mul_valS_mul LL S, mul_valS_add LL S, mul_lam1S_mul LL S, mul_lam1S_add LL S,
    (h R ι LL n S).1, (h R ι LL n S).2⟩

end Formalism.MainNotions.G.GLWeightTheory
end
end

