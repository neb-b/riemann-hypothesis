module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime
section
open Polynomial

namespace UpperTheory.V.J

private theorem cmpPrime_core {Λ B : Type} [CommRing Λ] [IsDomain Λ] [CommRing B] (φ : Λ →+* B)
    (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X])
    (tf : ∀ c : Λ, c ≠ 0 → ∀ a : B, φ c * a ∈ J → a ∈ J)
    (prim : ∀ a : B, ∃ c : Λ, c ≠ 0 ∧ ∃ P : Λ[X], φ c * a - P.eval₂ φ t ∈ J)
    (monic : ∀ i, (g i).Monic)
    (irr : ∀ i, Irreducible ((g i).map (algebraMap Λ (FractionRing Λ))))
    (inj : Function.Injective g)
    (kill : (∏ i, g i).eval₂ φ t ∈ J)
    (min : ∀ q : Λ[X], q.eval₂ φ t ∈ J → ∀ i, g i ∣ q) (i : Fin s) :
    (J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t}).IsPrime ∧
    (∀ q : Λ[X], q.eval₂ φ t ∈ J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t} ↔ g i ∣ q) ∧
    ∀ c : Λ, c ≠ 0 → φ c ∉ J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t} := by
  classical
  have finj : Function.Injective (algebraMap Λ (FractionRing Λ)) := IsFractionRing.injective Λ (FractionRing Λ)
  set e := (∏ j ∈ Finset.univ.erase i, g j).eval₂ φ t with he
  have memP : ∀ a : B, a ∈ J.colon {e} ↔ a * e ∈ J := by
    intro a
    simp [Submodule.mem_colon]
  have gprime : Prime ((g i).map (algebraMap Λ (FractionRing Λ))) := (irr i).prime
  have mapMonic : ∀ j, ((g j).map (algebraMap Λ (FractionRing Λ))).Monic := fun j => (monic j).map _
  have desc : ∀ q : Λ[X], g i ∣ q ↔
      (g i).map (algebraMap Λ (FractionRing Λ)) ∣ q.map (algebraMap Λ (FractionRing Λ)) := fun q =>
    (Polynomial.map_dvd_map (algebraMap Λ (FractionRing Λ)) finj (monic i)).symm
  have notdvd : ¬ (g i).map (algebraMap Λ (FractionRing Λ)) ∣
      (∏ j ∈ Finset.univ.erase i, g j).map (algebraMap Λ (FractionRing Λ)) := by
    rw [Polynomial.map_prod]
    intro h
    have exists_dvd : ∀ (S : Finset (Fin s)),
        (g i).map (algebraMap Λ (FractionRing Λ)) ∣
          ∏ j ∈ S, (g j).map (algebraMap Λ (FractionRing Λ)) →
        ∃ j ∈ S, (g i).map (algebraMap Λ (FractionRing Λ)) ∣
          (g j).map (algebraMap Λ (FractionRing Λ)) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false]
        exact fun hd => gprime.not_isUnit (isUnit_iff_dvd_one.mpr hd)
      | @insert a S ha ih =>
        simp only [Finset.prod_insert ha, Finset.mem_insert]
        intro hd
        rcases gprime.dvd_or_dvd hd with hd | hd
        · exact ⟨a, Or.inl rfl, hd⟩
        · obtain ⟨j, hj, hdj⟩ := ih hd
          exact ⟨j, Or.inr hj, hdj⟩
    obtain ⟨j, hj, hdvd⟩ := exists_dvd _ h
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hassoc := (irr i).associated_of_dvd (irr j) hdvd
    have heq := Polynomial.eq_of_monic_of_associated (mapMonic i) (mapMonic j) hassoc
    exact hji (inj (Polynomial.map_injective _ finj heq)).symm
  have key : ∀ q : Λ[X], q.eval₂ φ t ∈ J.colon {e} ↔ g i ∣ q := by
    intro q
    rw [memP, he, ← Polynomial.eval₂_mul]
    constructor
    · intro hq
      have h1 := min _ hq i
      rw [desc] at h1 ⊢
      rw [Polynomial.map_mul] at h1
      exact (gprime.dvd_or_dvd h1).resolve_right notdvd
    · rintro ⟨a, rfl⟩
      have hre : g i * a * ∏ j ∈ Finset.univ.erase i, g j = a * ∏ j, g j := by
        rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)]
        ring
      rw [hre, Polynomial.eval₂_mul]
      exact J.mul_mem_left _ kill
  have nunit : ∀ c : Λ, c ≠ 0 → φ c ∉ J.colon {e} := by
    intro c hc hmem
    have hC : (Polynomial.C c).eval₂ φ t ∈ J.colon {e} := by simpa using hmem
    rw [key] at hC
    have hdeg := Polynomial.natDegree_le_of_dvd hC (Polynomial.C_ne_zero.2 hc)
    rw [Polynomial.natDegree_C] at hdeg
    have h1 : g i = 1 := Polynomial.eq_one_of_monic_natDegree_zero (monic i) (by omega)
    apply (irr i).not_isUnit
    rw [h1, Polynomial.map_one]
    exact isUnit_one
  have scal : ∀ (c : Λ) (a : B), c ≠ 0 → (φ c * a ∈ J.colon {e} ↔ a ∈ J.colon {e}) := by
    intro c a hc
    rw [memP, memP, mul_assoc]
    exact ⟨tf c hc _, fun h => J.mul_mem_left _ h⟩
  have sub : ∀ x y : B, x - y ∈ J → (x ∈ J.colon {e} ↔ y ∈ J.colon {e}) := by
    intro x y hxy
    rw [memP, memP]
    have hd : x * e - y * e ∈ J := by rw [← sub_mul]; exact J.mul_mem_right _ hxy
    constructor
    · intro hx
      have h2 := J.sub_mem hx hd
      simpa using h2
    · intro hy
      have h2 := J.add_mem hd hy
      simpa using h2
  refine ⟨⟨?_, ?_⟩, key, nunit⟩
  · rw [Ideal.ne_top_iff_one]
    have h1 := nunit 1 one_ne_zero
    simpa using h1
  · intro a b hab
    obtain ⟨c, hc, Pa, ha⟩ := prim a
    obtain ⟨d, hd, Pb, hb⟩ := prim b
    have hab' : φ (c * d) * (a * b) ∈ J.colon {e} := Ideal.mul_mem_left _ _ hab
    have e1 : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t ∈ J := by
      have hre : φ (c * d) * (a * b) - (Pa * Pb).eval₂ φ t
          = (φ c * a - Pa.eval₂ φ t) * (φ d * b) + Pa.eval₂ φ t * (φ d * b - Pb.eval₂ φ t) := by
        rw [Polynomial.eval₂_mul, map_mul]
        ring
      rw [hre]
      exact J.add_mem (J.mul_mem_right _ ha) (J.mul_mem_left _ hb)
    rw [sub _ _ e1, key, desc, Polynomial.map_mul] at hab'
    rcases gprime.dvd_or_dvd hab' with h | h
    · left
      rw [← scal c a hc, sub _ _ ha, key, desc]
      exact h
    · right
      rw [← scal d b hd, sub _ _ hb, key, desc]
      exact h

theorem cmpPrime : CmpPrime := by
  intro O Λ B _ _ _ _ _ _ lam J t s g h i
  exact cmpPrime_core (lam : Λ →+* B) J t g h.tf h.prim h.monic h.irr h.inj h.kill h.min i

end UpperTheory.V.J
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.FactEx
section
open Polynomial UniqueFactorizationMonoid in
theorem UpperTheory.V.J.factEx :
    UpperTheory.V.J.FactEx := by
  intro Λ _ _ _ χ hχ
  classical
  have hinjK : Function.Injective (algebraMap Λ (FractionRing Λ)) :=
    IsFractionRing.injective Λ (FractionRing Λ)
  have hinj : Function.Injective (Polynomial.map (algebraMap Λ (FractionRing Λ))) :=
    Polynomial.map_injective _ hinjK
  set P := χ.map (algebraMap Λ (FractionRing Λ)) with hPdef
  have hP : P ≠ 0 := (hχ.map _).ne_zero
  have hmon : ∀ f ∈ normalizedFactors P, f.Monic := by
    intro f hf
    rw [← normalize_normalized_factor f hf]
    exact Polynomial.monic_normalize (prime_of_normalized_factor f hf).ne_zero
  have hlift : ∀ f ∈ normalizedFactors P,
      ∃ g : Λ[X], g.Monic ∧ g.map (algebraMap Λ (FractionRing Λ)) = f := by
    intro f hf
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing Λ) hχ
      (dvd_of_mem_normalizedFactors hf)
    rw [(hmon f hf).leadingCoeff, C_1, mul_one] at hg
    refine ⟨g, Polynomial.monic_of_injective hinjK ?_, hg⟩
    rw [hg]
    exact hmon f hf
  choose! L hLm hLmap using hlift
  have hprod : χ = ((normalizedFactors P).map L).prod := by
    apply hinj
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    have h1 : (normalizedFactors P).map
        ((Polynomial.map (algebraMap Λ (FractionRing Λ))) ∘ L) = normalizedFactors P := by
      conv_rhs => rw [← Multiset.map_id (normalizedFactors P)]
      exact Multiset.map_congr rfl (fun f hf => hLmap f hf)
    rw [h1]
    refine eq_of_monic_of_associated (hχ.map _) ?_ (prod_normalizedFactors hP).symm
    exact Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) monic_one hmon
  have memG : ∀ x ∈ (normalizedFactors P).map L,
      x.Monic ∧ Irreducible (x.map (algebraMap Λ (FractionRing Λ))) := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨hLm f hf, by rw [hLmap f hf]; exact irreducible_of_normalized_factor f hf⟩
  let e := ((normalizedFactors P).map L).toFinset.equivFin
  refine ⟨_, fun i => (e.symm i).1, fun i => ((normalizedFactors P).map L).count (e.symm i).1,
    ⟨fun i => (memG _ (Multiset.mem_toFinset.1 (e.symm i).2)).1,
     fun i => (memG _ (Multiset.mem_toFinset.1 (e.symm i).2)).2,
     fun i j h => e.symm.injective (Subtype.ext h),
     fun i => Multiset.count_pos.2 (Multiset.mem_toFinset.1 (e.symm i).2), ?_⟩⟩
  refine hprod.trans ?_
  rw [Finset.prod_multiset_count, ← Finset.prod_coe_sort]
  exact Fintype.prod_equiv e _ _ (fun x => by simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IntMod
section
open Polynomial

namespace UpperTheory.V.J

section

variable {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
  (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M]
  (hs : ∀ (a : Λ) (m : M), a • m = lam a • m)

private theorem actL_pow (a : B) (n : ℕ) (m : M) :
    ((actL lam M hs a) ^ n) m = (a ^ n) • m := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_smul]
    rfl

private theorem act_eval (a : B) (q : Λ[X]) (m : M) :
    q.eval₂ (lam : Λ →+* B) a • m = (aeval (actL lam M hs a) q) m := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [eval₂_add, add_smul, hp, hr, map_add (f := _), LinearMap.add_apply]
  · rw [eval₂_monomial, aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      actL_pow, mul_smul, hs]
    rfl

end

end UpperTheory.V.J

theorem UpperTheory.V.J.intMod :
    UpperTheory.V.J.IntMod := by
  intro O Λ B _ _ _ _ _ _ lam J M _ _ _ d a
  have := d.free
  have := d.fin
  refine ⟨(actL lam M d.hs a).charpoly, (actL lam M d.hs a).charpoly_monic, ?_⟩
  have hann : eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro m
    rw [act_eval lam M d.hs, LinearMap.aeval_self_charpoly]
    rfl
  generalize eval₂ (lam : Λ →+* B) a (actL lam M d.hs a).charpoly = x at hann ⊢
  rw [← d.rad.radical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro p ⟨hJp, hp⟩
  exact (d.supp p hp).2 hJp hann
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LeJoint
section
open Polynomial TensorProduct

namespace UpperTheory.V.J

section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private lemma ev_uniq (f : Module.End K V) {μ ν : K} {v : V} (hv : v ≠ 0)
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ f.maxGenEigenspace ν) : μ = ν := by
  by_contra hne
  have hd := Module.End.disjoint_genEigenspace f hne ⊤ ⊤
  exact hv ((Submodule.disjoint_def.1 hd) v h1 h2)

private theorem ev_add_lemma {X Y : Module.End K V} (hc : Commute X Y) {v : V} {k l : ℕ}
    (hk : (X ^ k) v = 0) (hl : (Y ^ l) v = 0) : ((X + Y) ^ (k + l)) v = 0 := by
  rw [hc.add_pow, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro m _
  have hXY : (X ^ m * Y ^ (k + l - m)) v = 0 := by
    by_cases hmk : k ≤ m
    · rw [(hc.pow_pow m (k + l - m)).eq, Module.End.mul_apply, ← pow_sub_mul_pow X hmk,
        Module.End.mul_apply, hk, map_zero, map_zero]
    · rw [show k + l - m = (k + l - m - l) + l by omega, pow_add, Module.End.mul_apply,
        Module.End.mul_apply, hl, map_zero, map_zero]
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hXY, smul_zero]

private lemma ev_add {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V}
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ g.maxGenEigenspace ν) :
    v ∈ (f + g).maxGenEigenspace (μ + ν) := by
  rw [Module.End.mem_maxGenEigenspace] at h1 h2 ⊢
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have hs1 : ∀ (c : K) (T : Module.End K V), Commute (c • (1 : Module.End K V)) T := fun c T => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commute_algebraMap_left c T
  have hc : Commute (f - μ • 1) (g - ν • 1) := (h.sub_right (hs1 ν f).symm).sub_left (hs1 μ _)
  refine ⟨k + l, ?_⟩
  have hsplit : f + g - (μ + ν) • (1 : Module.End K V) = (f - μ • 1) + (g - ν • 1) := by
    rw [add_smul]
    abel
  rw [hsplit]
  exact ev_add_lemma hc hk hl

private lemma ev_mul {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V}
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ g.maxGenEigenspace ν) :
    v ∈ (f * g).maxGenEigenspace (μ * ν) := by
  rw [Module.End.mem_maxGenEigenspace] at h1 h2 ⊢
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have hs1 : ∀ (c : K) (T : Module.End K V), Commute (c • (1 : Module.End K V)) T := fun c T => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commute_algebraMap_left c T
  have hag : Commute (f - μ • 1) g := h.sub_left (hs1 μ g)
  have hab : Commute (f - μ • 1) (g - ν • 1) := (h.sub_right (hs1 ν f).symm).sub_left (hs1 μ _)
  have hgb : Commute g (g - ν • 1) := (Commute.refl g).sub_right (hs1 ν g).symm
  have hc : Commute ((f - μ • 1) * g) (μ • (g - ν • 1)) := (hab.mul_left hgb).smul_right μ
  have hsplit : f * g - (μ * ν) • (1 : Module.End K V) = (f - μ • 1) * g + μ • (g - ν • 1) := by
    simp only [sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul]
    abel
  refine ⟨k + l, ?_⟩
  rw [hsplit]
  refine ev_add_lemma hc ?_ ?_
  · rw [hag.mul_pow, (hag.pow_pow k k).eq, Module.End.mul_apply, hk, map_zero]
  · rw [_root_.smul_pow, LinearMap.smul_apply, hl, smul_zero]

private lemma ev_scal (c : K) (v : V) : v ∈ (c • (1 : Module.End K V)).maxGenEigenspace c :=
  (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp⟩

private lemma le_joint {ι : Type} [FiniteDimensional K V] [IsAlgClosed K] (f : ι → Module.End K V)
    (hc : ∀ i j, Commute (f i) (f j)) (x : ι → K) (t : ι)
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, v ∈ (f i).maxGenEigenspace (χ i)) → χ t = x t → χ = x) :
    (f t).maxGenEigenspace (x t) ≤ ⨅ i, (f i).maxGenEigenspace (x i) := by
  classical
  have hmap : ∀ j, Set.MapsTo (f j) ((f t).maxGenEigenspace (x t)) ((f t).maxGenEigenspace (x t)) :=
    fun j => Module.End.mapsTo_maxGenEigenspace_of_comm (hc t j) (x t)
  have lift : ∀ (j : ι) (μ : K) (w : (f t).maxGenEigenspace (x t)),
      w ∈ Module.End.maxGenEigenspace ((f j).restrict (hmap j)) μ → (w : V) ∈ (f j).maxGenEigenspace μ := by
    intro j μ w hw
    have e := Module.End.genEigenspace_restrict (f j) ((f t).maxGenEigenspace (x t)) ⊤ μ (hmap j)
    have hw' : w ∈ Submodule.comap ((f t).maxGenEigenspace (x t)).subtype (((f j).genEigenspace μ) ⊤) := e ▸ hw
    exact hw'
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
    (fun j => (f j).restrict (hmap j))
    (fun i j φ => Module.End.mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f i) (f j) (hmap i) (hmap j)
      (Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ))
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hbot : ∀ χ : ι → K, χ ≠ x →
      ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (χ j) = ⊥ := by
    intro χ hχ
    by_contra hne
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
    rw [Submodule.mem_iInf] at hw
    have hv0 : (w : V) ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
    have hall : ∀ j, (w : V) ∈ (f j).maxGenEigenspace (χ j) := fun j => lift j (χ j) w (hw j)
    have hχt : χ t = x t := ev_uniq (f t) hv0 (hall t) w.2
    exact hχ (h χ w hv0 hall hχt)
  have heq : ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (x j) = ⊤ := by
    rw [eq_top_iff, ← htop]
    apply iSup_le
    intro χ
    by_cases hχ : χ = x
    · rw [hχ]
    · rw [hbot χ hχ]
      exact bot_le
  intro v hv
  rw [Submodule.mem_iInf]
  intro j
  have hw : (⟨v, hv⟩ : (f t).maxGenEigenspace (x t)) ∈
      ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (x j) := by
    rw [heq]
    exact Submodule.mem_top
  rw [Submodule.mem_iInf] at hw
  exact lift j (x j) ⟨v, hv⟩ (hw j)

end

end UpperTheory.V.J

theorem UpperTheory.V.J.muGe :
    UpperTheory.V.J.MuGe := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ lam J M _ _ _ _ _ h x t hsep
  letI : Algebra Λ K := (x.comp lam).toAlgebra
  have actAdd : ∀ a b : B, actL lam M h.hs (a + b) = actL lam M h.hs a + actL lam M h.hs b :=
    fun a b => LinearMap.ext fun m => add_smul a b m
  have actMul : ∀ a b : B, actL lam M h.hs (a * b) = actL lam M h.hs a * actL lam M h.hs b :=
    fun a b => LinearMap.ext fun m => mul_smul a b m
  have Jrad : J ≤ (Module.annihilator B M).radical := by
    intro y hy
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro p ⟨hap, hp⟩
    exact ((h.supp p hp).1 hap) hy
  let F : B → Module.End K (K ⊗[Λ] M) := fun a => LinearMap.baseChange K (actL lam M h.hs a)
  have Fadd : ∀ a b, F (a + b) = F a + F b := fun a b => by
    simp only [F, actAdd, LinearMap.baseChange_add]
  have Fmul : ∀ a b, F (a * b) = F a * F b := fun a b => by
    simp only [F, actMul, LinearMap.baseChange_mul]
  have Fcomm : ∀ a b, Commute (F a) (F b) := fun a b => by
    show F a * F b = F b * F a
    rw [← Fmul, ← Fmul, mul_comm]
  have Flam : ∀ l : Λ, F (lam l) = (x (lam l)) • (1 : Module.End K (K ⊗[Λ] M)) := fun l => by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      show k ⊗ₜ[Λ] (lam l • m) = x (lam l) • (k ⊗ₜ[Λ] m)
      rw [← h.hs, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
      rfl
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw]
  have Fann : ∀ a ∈ Module.annihilator B M, F a = 0 := fun a ha => by
    have h0 : actL lam M h.hs a = 0 := LinearMap.ext fun m => (Module.mem_annihilator.1 ha) m
    simp only [F, h0, LinearMap.baseChange_zero]
  have key : rootMultiplicity (x t) (Polynomial.map (↑(x.comp lam) : Λ →+* K)
      (LinearMap.charpoly (actL lam M h.hs t))) = Module.finrank K ((F t).maxGenEigenspace (x t)) := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.charpoly_baseChange]
    rfl
  refine (le_of_eq key).trans ?_
  show _ ≤ Module.finrank K ↥(⨅ a, (F a).maxGenEigenspace (x a))
  apply Submodule.finrank_mono
  refine le_joint F (fun a b => Fcomm a b) x t ?_
  intro χ v hv hall hχt
  have uniq : ∀ a μ, v ∈ (F a).maxGenEigenspace μ → μ = χ a := fun a μ hμ => ev_uniq (F a) hv hμ (hall a)
  have χlam : ∀ l, χ (lam l) = x (lam l) := fun l => (uniq _ _ (by rw [Flam]; exact ev_scal _ v)).symm
  let x' : B →ₐ[O] K :=
    { toFun := χ
      map_one' := by
        have e := χlam 1
        rwa [map_one, map_one] at e
      map_mul' := fun a b =>
        (uniq (a * b) (χ a * χ b) (by rw [Fmul]; exact ev_mul (Fcomm a b) (hall a) (hall b))).symm
      map_zero' := by
        have e := χlam 0
        rwa [map_zero, map_zero] at e
      map_add' := fun a b =>
        (uniq (a + b) (χ a + χ b) (by rw [Fadd]; exact ev_add (Fcomm a b) (hall a) (hall b))).symm
      commutes' := fun c => by
        show χ (algebraMap O B c) = algebraMap O K c
        rw [← lam.commutes c, χlam, lam.commutes c, x.commutes c] }
  have hJ : J ≤ RingHom.ker x' := by
    intro j hj
    rw [RingHom.mem_ker]
    obtain ⟨n, hn⟩ := Jrad hj
    have h0 : χ (j ^ n) = 0 := by
      refine (uniq (j ^ n) 0 ?_).symm
      rw [Fann _ hn]
      have e := ev_scal (0 : K) v
      rwa [zero_smul] at e
    have h1 : x' (j ^ n) = 0 := h0
    rw [map_pow] at h1
    exact (pow_eq_zero_iff'.mp h1).1
  have hx := hsep x' hJ (AlgHom.ext fun l => χlam l) hχt
  funext a
  exact DFunLike.congr_fun hx a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MuLe
section
open Polynomial TensorProduct

theorem UpperTheory.V.J.muLe :
    UpperTheory.V.J.MuLe := by
  intro O Λ B K _ _ _ _ _ _ _ _ lam M _ _ _ _ _ hs y t
  unfold UpperTheory.V.J.mu
  refine (Submodule.finrank_mono (iInf_le _ t)).trans ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.charpoly_baseChange]
  rfl
end

