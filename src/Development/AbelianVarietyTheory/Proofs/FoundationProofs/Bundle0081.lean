module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import ReciprocityTheory.GaloisValuations.Global
public import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankRangeLeSumThreeComplements
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem finrank_range_le_three (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (P a b : Module.End ℂ M) :
    Module.finrank ℂ (LinearMap.range P) ≤ Module.finrank ℂ (LinearMap.range (a * b * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - a) * P)) +
      Module.finrank ℂ (LinearMap.range ((1 - b) * P)) := by
  have hle : LinearMap.range P ≤ (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P)) ⊔
      (LinearMap.range ((1 - b) * P)).map a := by
    rintro _ ⟨x, rfl⟩
    have hx : P x = ((a * b * P) x + ((1 - a) * P) x) + a (((1 - b) * P) x) := by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x))
      (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ x))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P) ⊔ LinearMap.range ((1 - a) * P))
    ((LinearMap.range ((1 - b) * P)).map a)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range (a * b * P)) (LinearMap.range ((1 - a) * P))
  have h4 := Submodule.finrank_map_le a (LinearMap.range ((1 - b) * P))
  omega

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedCycModOfFixedCycZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory

theorem fixed_cycMod_of_fixed_cycZ : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (F : Finset Ω) (y : Ω), (∀ s ∈ Ine (F := ℚ) A, (∀ z ∈ F, s z = z) → cycZ ℚ Ω l s = 1 → s y = y) →
  ∃ m : ℕ, ∀ s : G ℚ Ω, s ∈ Ine (F := ℚ) A ∧ (∀ z ∈ F, s z = z) ∧ cycMod ℚ Ω l m s = 1 → s y = y := by
  intro l _ Ω _ _ _ A _ F y hy
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic

  set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({y} : Set Ω) with hK
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hSo : IsOpen (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
    intro g hg
    exact (IntermediateField.mem_fixingSubgroup_iff K g).mp hg y
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton y))
  set S : Set (G ℚ Ω) := (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) with hS
  have memS : ∀ s : G ℚ Ω, s ∈ S ↔ s y = y := fun s => Iff.rfl
  set H0 : Set (G ℚ Ω) := (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩ ⋂ z ∈ F, {s : G ℚ Ω | s z = z} with hH0
  have hH0c : IsClosed H0 :=
    (isClosed_Ine A).inter (isClosed_biInter fun z _ => isClosed_setOf_apply z (fun t => t = z))

  have hcm : ∀ (m : ℕ) (s : G ℚ Ω), cycMod ℚ Ω l m s = 1 ↔
      PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro m s; rw [Units.ext_iff]; rfl
  set C : ℕ → Set (G ℚ Ω) := fun m =>
    (H0 ∩ {s | PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1}) ∩ Sᶜ with hC
  have hCc : ∀ m, IsClosed (C m) := by
    intro m
    have hc : Continuous fun s : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
      (GroundTheory.Global.Cyclotomic.continuous_toZModPow m).comp
        (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
    exact (hH0c.inter ((isClosed_discrete ({1} : Set (ZMod (l ^ m)))).preimage hc)).inter
      hSo.isClosed_compl
  have hmono : ∀ m k, m ≤ k → C k ⊆ C m := by
    intro m k hmk s ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨h0, ?_⟩, h2⟩
    simp only [Set.mem_setOf_eq] at h1 ⊢
    rw [← PadicInt.zmod_cast_comp_toZModPow m k hmk, RingHom.comp_apply, h1, map_one]
  by_contra hne
  push_neg at hne
  have hCn : ∀ m, (C m).Nonempty := by
    intro m
    obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := hne m
    refine ⟨s, ⟨⟨hs1, ?_⟩, (hcm m s).mp hs3⟩, hs4⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact hs2
  have hdir : Directed (· ⊇ ·) C := fun m k =>
    ⟨max m k, hmono m _ (le_max_left m k), hmono k _ (le_max_right m k)⟩
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCn
    (fun m => (hCc m).isCompact) hCc
  simp only [Set.mem_iInter] at hs
  obtain ⟨⟨h0i, h0f⟩, -⟩ := (hs 0).1
  have hz : cycZ ℚ Ω l s = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [(hs n).1.2, Units.val_one, map_one]
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at h0f
  exact (hs 0).2 ((memS s).mpr (hy s h0i h0f hz))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTower
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

def IsPowModP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) (p : ℕ)
    (x : A) : Prop :=
  ∃ y ∈ S, ∃ z ∈ S, x = y ^ p + (p : A) * z

section Closure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {p : ℕ}

theorem isPthPowerModP_add (hp : p.Prime) {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x + x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨y, hy⟩ : S) ⟨y', hy'⟩
  have hr' := congrArg Subtype.val hr
  push_cast at hr'
  refine ⟨y + y', S.add_mem hy hy', z + z' - y * y' * r, ?_, ?_⟩
  · exact S.sub_mem (S.add_mem hz hz') (S.mul_mem (S.mul_mem hy hy') r.2)
  · rw [hr']; ring

theorem isPthPowerModP_mul {x x' : A} (hx : IsPowModP S p x) (hx' : IsPowModP S p x') :
    IsPowModP S p (x * x') := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨y', hy', z', hz', rfl⟩ := hx'
  refine ⟨y * y', S.mul_mem hy hy', z * y' ^ p + y ^ p * z' + (p : A) * z * z', ?_, ?_⟩
  · refine S.add_mem (S.add_mem (S.mul_mem hz (S.pow_mem hy' _))
      (S.mul_mem (S.pow_mem hy _) hz')) (S.mul_mem (S.mul_mem ?_ hz) hz')
    exact S.natCast_mem p
  · ring

theorem isPthPowerModP_pow {y : A} (hy : y ∈ S) : IsPowModP S p (y ^ p) :=
  ⟨y, hy, 0, S.zero_mem, by ring⟩

theorem isPthPowerModP_zero (hp : p.Prime) : IsPowModP S p 0 :=
  ⟨0, S.zero_mem, 0, S.zero_mem, by rw [zero_pow hp.ne_zero]; ring⟩

theorem isPthPowerModP_add_p_mul {x h : A} (hx : IsPowModP S p x) (hh : h ∈ S) :
    IsPowModP S p (x + (p : A) * h) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact ⟨y, hy, z + h, S.add_mem hz hh, by ring⟩

end Closure

theorem frob_surj_adjoin_tower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
      ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  intro p hp Ω _ _ T x hx
  set S := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) with hS
  have hpp : p.Prime := hp.out
  have hζ : ∀ n, T.ζ n ∈ S := fun n => Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩)
  have hq : ∀ n, T.qq n ∈ S := fun n => Algebra.subset_adjoin (Or.inr ⟨n, rfl⟩)
  suffices IsPowModP S p x from this
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [← T.ζpow n]; exact isPthPowerModP_pow S (hζ _)
    · rw [← T.qpow n]; exact isPthPowerModP_pow S (hq _)
  | algebraMap r =>
    obtain ⟨g, h, rfl⟩ := _root_.GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul p r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_mul, map_natCast]
    refine isPthPowerModP_add_p_mul S ?_ ?_
    · refine Finset.sum_induction _ (IsPowModP S p) (fun a b ha hb => isPthPowerModP_add S hpp ha hb)
        (isPthPowerModP_zero S hpp) ?_
      intro j _
      have e : algebraMap (O0 p) Ω (qO p ^ (j : ℕ) * g j ^ p) =
          (T.qq 1 ^ (j : ℕ) * algebraMap (O0 p) Ω (g j)) ^ p := by
        rw [map_mul, map_pow, map_pow, ← T.q0, ← T.qpow 0, mul_pow, ← pow_mul, ← pow_mul, mul_comm p]
      rw [e]
      exact isPthPowerModP_pow S (S.mul_mem (S.pow_mem (hq 1) _) (S.algebraMap_mem _))
    · exact S.algebraMap_mem _
  | add x y _ _ hx hy => exact isPthPowerModP_add S hpp hx hy
  | mul x y _ _ hx hy => exact isPthPowerModP_mul S hx hy

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRelationOfFrobApprox
section
open GlobalTheory.KZ Matrix

namespace GlobalTheory

theorem galois_relation_of_frob_approx : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Type} [NormedField E] (r : ℕ) (A : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin r) (Fin r) E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (v : Fin r → E), (∀ (s : Ω ≃ₐ[ℚ] Ω) (δ : ℝ), 0 < δ → ∃ E0 : Finset Ω, ∀ s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → (∀ i j, ‖A (s * s') i j - A s i j‖ < δ) ∧ ‖t (s * s') - t s‖ < δ ∧ ‖d (s * s') - d s‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s, FrobAt q s → ∀ i, ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < δ) → (∀ (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ), ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s')) → ∀ s, A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v = 0 := by
  intro Ω _ _ E _ r A t d v hcont happrox hdens s
  funext i

  let G : (Fin r → Fin r → E) × E × E → E := fun x =>
    (Matrix.of x.1 *ᵥ (Matrix.of x.1 *ᵥ v) - x.2.1 • (Matrix.of x.1 *ᵥ v) + x.2.2 • v) i
  have hG : Continuous G := by
    simp only [G, Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    fun_prop
  have key : ∀ ε : ℝ, 0 < ε → ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hGη⟩ := Metric.continuous_iff.mp hG (fun a b => A s a b, t s, d s) (ε / 2) (by linarith)
    obtain ⟨E0, hE0⟩ := hcont s η hη
    obtain ⟨S, hS⟩ := happrox (ε / 2) (by linarith)
    obtain ⟨s', q, hfix, hq, hqS, hfr⟩ := hdens s E0 S
    obtain ⟨hA, ht, hd⟩ := hE0 s' hfix
    have h1 := hS q hq hqS (s * s') hfr i
    have hdist : dist (fun a b => A (s * s') a b, t (s * s'), d (s * s')) (fun a b => A s a b, t s, d s) < η := by
      rw [Prod.dist_eq, Prod.dist_eq]
      refine max_lt ?_ (max_lt ?_ ?_)
      · rw [dist_pi_lt_iff hη]; intro a
        rw [dist_pi_lt_iff hη]; intro b
        rw [dist_eq_norm]; exact hA a b
      · rw [dist_eq_norm]; exact ht
      · rw [dist_eq_norm]; exact hd
    have h2 := hGη _ hdist
    have e1 : G (fun a b => A (s * s') a b, t (s * s'), d (s * s')) = (A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i := rfl
    have e2 : G (fun a b => A s a b, t s, d s) = (A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i := rfl
    rw [e1, e2, dist_eq_norm] at h2
    have := norm_sub_le_norm_sub_add_norm_sub ((A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i) ((A (s * s') *ᵥ (A (s * s') *ᵥ v) - t (s * s') • (A (s * s') *ᵥ v) + d (s * s') • v) i) 0
    rw [norm_sub_rev] at h2
    simp only [sub_zero] at this
    linarith
  have : ‖(A s *ᵥ (A s *ᵥ v) - t s • (A s *ᵥ v) + d s • v) i‖ = 0 := by
    by_contra h
    have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    exact lt_irrefl _ (key _ hpos)
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlEqOneOfPowPrimePow
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem end_eq_one_of_pow_prime {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {p : ℕ} (hp : p.Prime) (hV : Module.finrank ℚ V + 1 < p) (f : Module.End ℚ V)
    (hf : f ^ p = 1) : f = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hf]
  have hdeg : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ V := by
    rw [← LinearMap.charpoly_natDegree f]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.pos
  have hne : minpoly ℚ f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral f)
  have hnd : ¬ cyclotomic p ℚ ∣ minpoly ℚ f := by
    intro h
    have h2 := natDegree_le_of_dvd h hne
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    omega
  have hcop : IsCoprime (minpoly ℚ f) (cyclotomic p ℚ) :=
    ((hirr.coprime_iff_not_dvd).2 hnd).symm
  have h3 : minpoly ℚ f ∣ X - 1 := hcop.dvd_of_dvd_mul_left h1
  obtain ⟨q, hq⟩ := h3
  have h4 : aeval f (X - 1 : ℚ[X]) = 0 := by
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

theorem gl_eq_one_of_pow_prime (E : Type) [Field E] [NumberField E] (N p : ℕ) (hp : p.Prime)
    (h : Module.finrank ℚ E * N + 1 < p) (γ : GL (Fin N) E) (hγ : γ ^ p = 1) : γ = 1 := by
  have hfin : Module.finrank ℚ (Fin N → E) = Module.finrank ℚ E * N := by
    rw [← Module.finrank_mul_finrank ℚ E (Fin N → E)]
    simp
  have hM : (γ : Matrix (Fin N) (Fin N) E) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hγ, Units.val_one]
  have hg : (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hM, Matrix.toLin'_one]; rfl
  have hf : ((Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)).restrictScalars ℚ :
      Module.End ℚ (Fin N → E)) ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hg v
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h1 := end_eq_one_of_pow_prime hp (by rw [hfin]; exact h) _ hf
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one]
  exact LinearMap.ext fun v => LinearMap.congr_fun h1 v

theorem gl_eq_one_of_pow_prime_pow :
    ∀ (E : Type) [Field E] [NumberField E] (N p : ℕ), p.Prime →
      Module.finrank ℚ E * N + 1 < p → ∀ γ : GL (Fin N) E, ∀ a : ℕ, γ ^ (p ^ a) = 1 → γ = 1 := by
  intro E _ _ N p hp h γ a
  induction a with
  | zero => intro h0; simpa using h0
  | succ a ih =>
    intro h0
    apply ih
    apply gl_eq_one_of_pow_prime E N p hp h
    rw [← pow_mul, ← pow_succ]
    exact h0

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MobLaws

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h0
  have hy : 0 < z.im := hz
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hd := det_pos g
  rcases him with hc | hc
  · rw [hc] at hre hd; simp at hre; rw [hre] at hd; simp at hd
  · linarith

theorem im_mob (g : GQ) (z : ℂ) : (mob g z).im =
    (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
  rw [mob, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  rw [div_sub_div_same]
  congr 1
  ring

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  show 0 < (mob g z).im
  rw [im_mob]
  have hy : 0 < z.im := hz
  have hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast det_pos g
  exact div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))

theorem complex_mobius_fraction_clear_denom (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  have e1 : a * (N / D) + b = (a * N + b * D) / D := by field_simp
  have e2 : c * (N / D) + d = (c * N + d * D) / D := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have h1 := den_ne h hz
  unfold mob
  rw [complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]
  simp only [ent_mul]
  push_cast
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold mob
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; norm_num
  apply Subtype.ext; apply Units.ext; ext i j
  simp [toGQ, h, ofSL]

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  apply Subtype.ext; apply Units.ext
  simp only [toGQ, h, hm, hm', dif_pos]
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.KZ.MobLaws

namespace GlobalTheory.KZ

theorem mob_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') :=
  ⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one,
    MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCoeffEqZero
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory

theorem homogeneous_poly_coeff_eq_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (htf : ∀ (c : ℤ_[l]) (x : M), c ≠ 0 → c • x = 0 → x = 0) (w : ℕ) (c : Fin (w + 1) → M)
    (hv : ∀ u : Fin 2 → ℤ_[l], ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i = 0) :
    c = 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] := Matrix.vandermonde (fun t : Fin (w + 1) => ((t : ℕ) : ℤ_[l])) with hVdef
  have hrow : ∀ t : Fin (w + 1), ∑ i, V t i • c i = 0 := by
    intro t
    have := hv ![((t : ℕ) : ℤ_[l]), 1]
    simpa [hVdef, Matrix.vandermonde_apply] using this
  have hdet : V.det ≠ 0 := by
    rw [hVdef, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    apply Fin.ext
    have hab' : ((a : ℕ) : ℤ_[l]) = ((b : ℕ) : ℤ_[l]) := hab
    exact_mod_cast hab'
  have key : ∀ j, V.det • c j = 0 := by
    intro j
    have h1 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = 0 := by simp [hrow]
    have h2 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = ∑ i, (V.adjugate * V) j i • c i := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
    rw [h2, Matrix.adjugate_mul] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq] using h1
  funext j
  exact htf _ _ hdet (key j)

end GlobalTheory
end

