module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0017
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0018

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.DeltaIntegralEnvelopingStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def nablaToDeltaMaps (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O (Module.End (KK O) V) where
  carrier := {f | ∀ x ∈ Nabla (O := O) E lam v, f x ∈ Delta (O := O) E v}
  zero_mem' := fun x _ => by simp
  add_mem' := fun {f g} hf hg x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (hf x hx)

theorem nabla_integral_enveloping_stable (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) :
    UZStable (O := O) E (NablaSub (O := O) E lam v) := by
  intro u hu x hx u' hu'
  exact hx (u' * u) (Submonoid.mul_mem _ hu' (Submonoid.subset_closure hu))

theorem delta_integral_enveloping_stable (E : GLOps n (KK O) V) (v : V) : UZStable (O := O) E (Delta (O := O) E v) := by
  intro u hu x hx
  have hle : Delta (O := O) E v ≤ (Delta (O := O) E v).comap (u.restrictScalars O) := by
    unfold Delta
    rw [Submodule.span_le]
    rintro _ ⟨u', hu', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    exact Submodule.subset_span ⟨u * u', Submonoid.mul_mem _ (Submonoid.subset_closure hu) hu', rfl⟩
  exact hle hx

theorem adjoint_divided_power_expansion [CharZero (KK O)] (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) (f : Module.End (KK O) V) :
    divPowE (adjointEndAction E) a b k f =
      ∑ m ∈ range (k + 1), ((-1 : KK O) ^ (k - m)) • (divPowE E a b m * f * divPowE E a b (k - m)) := by
  have hc : Commute (LinearMap.mulLeft (KK O) (E a b)) ((-1 : KK O) • LinearMap.mulRight (KK O) (E a b)) :=
    (LinearMap.commute_mulLeft_right _ _).smul_right _
  have hsub : adjointEndAction E a b =
      LinearMap.mulLeft (KK O) (E a b) + (-1 : KK O) • LinearMap.mulRight (KK O) (E a b) := by
    rw [adjointEndAction, neg_one_smul, sub_eq_add_neg]
  simp only [divPowE]
  rw [hsub, hc.add_pow, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := by simp at hm; omega
  rw [smul_pow, LinearMap.pow_mulLeft, LinearMap.pow_mulRight]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, map_nsmul, map_smul, smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [← Nat.cast_smul_eq_nsmul (KK O), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose (KK O) hmk]
  have h1 : ((m.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (((k - m).factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - m)
  have h3 : ((k.factorial : ℕ) : KK O) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem nabla_to_delta_maps_stable [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    (lam : Fin n → ℤ) (v : V) : UZStable (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) := by
  intro u hu f hf x hx
  have hN := nabla_integral_enveloping_stable (O := O) E lam v
  have hD := delta_integral_enveloping_stable (O := O) E v
  have htop : ∀ z : V, z ∈ ⨆ mu, ⨆ (_ : True), weightSp E mu := by
    intro z
    simp only [iSup_true]
    rw [hE.2.2]
    exact Submodule.mem_top
  rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
  · rw [adjoint_divided_power_expansion, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply]
    have h1 : divPowE E a b (k - m) x ∈ NablaSub (O := O) E lam v := hN _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) x hx
    have h2 : f (divPowE E a b (k - m) x) ∈ Delta (O := O) E v := hf _ h1
    have h3 := hD _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ h2
    have h4 := intCast_smul_mem_submodule (Delta (O := O) E v) ((-1 : ℤ) ^ (k - m)) h3
    simpa using h4
  · have hR : ∀ (m : ℕ) (μ ν : Fin n → ℤ) (z : V), z ∈ weightSp E μ →
        (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) z =
          (∏ j ∈ range m, ((μ a : KK O) - ((ν a : KK O) + j))) • z := by
      intro m μ ν z hz
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          (mem_weightSpace_iff_diag_scalar.1 hz) a, ← sub_smul, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]
    have hw : ∀ (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        (binomE (adjointEndAction E) a k f) y = ∑ ij ∈ antidiagonal k,
          (((Ring.choose (-(ν a)) ij.2 : ℤ) : KK O)) • binomE E a ij.1 (f y) := by
      intro ν y hy
      have hadx : ∀ (g : Module.End (KK O) V) (c : KK O),
          ((adjointEndAction E a a - c • (1 : Module.End (KK O) (Module.End (KK O) V))) g) y =
            (E a a - ((ν a : KK O) + c) • (1 : Module.End (KK O) V)) (g y) := by
        intro g c
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, adjointEndAction_apply,
          Module.End.mul_apply, (mem_weightSpace_iff_diag_scalar.1 hy) a, map_smul, add_smul, LinearMap.add_apply]
        abel
      have hprod : ∀ (m : ℕ) (g : Module.End (KK O) V),
          (((List.range m).map fun j : ℕ => adjointEndAction E a a - (j : KK O) •
            (1 : Module.End (KK O) (Module.End (KK O) V))).prod g) y =
          (((List.range m).map fun j : ℕ => E a a - ((ν a : KK O) + j) • (1 : Module.End (KK O) V)).prod) (g y) := by
        intro m
        induction m with
        | zero => intro g; simp
        | succ m ih =>
          intro g
          rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
            List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton]
          simp only [Module.End.mul_apply]
          rw [ih, hadx]
      obtain ⟨G, h, hh, hfy⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop (f y))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [binomE, LinearMap.smul_apply, LinearMap.smul_apply, hprod, hfy, map_sum, Finset.smul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμw := (hh μ hμ).2
      rw [hR k μ ν _ hμw, smul_smul]
      simp only [binomial_diagonal_on_weight hμw, map_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      calc ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, ((μ a : KK O) - ((ν a : KK O) + j))
          = ((k.factorial : KK O))⁻¹ * ∏ j ∈ range k, (((μ a + -(ν a) : ℤ) : KK O) - (j : KK O)) := by
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            push_cast
            ring
        _ = ((Ring.choose (μ a + -(ν a)) k : ℤ) : KK O) := inv_factorial_prod_eq_choose _ _
        _ = _ := by
            rw [Ring.add_choose_eq k (Commute.all _ _)]
            push_cast
            refine Finset.sum_congr rfl fun ij _ => ?_
            ring
    obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Module.End (KK O) V,
        S = fun j : ℕ => ((((j : ℤ).negOnePow : ℤˣ) : ℤ) : KK O) • shiftedBinomialOperator E a ((j : ℤ) - 1) j := ⟨_, rfl⟩
    have hS : ∀ (j : ℕ) (ν : Fin n → ℤ) (y : V), y ∈ weightSp E ν →
        S j y = ((Ring.choose (-(ν a)) j : ℤ) : KK O) • y := by
      intro j ν y hy
      rw [hSdef, LinearMap.smul_apply, shifted_binomial_on_weight hy, smul_smul]
      congr 1
      rw [Ring.choose_neg, Units.smul_def, smul_eq_mul, add_sub_assoc]
      push_cast
      ring
    have hop : binomE (adjointEndAction E) a k f = ∑ ij ∈ antidiagonal k, binomE E a ij.1 * f * S ij.2 := by
      apply LinearMap.ext
      intro z
      obtain ⟨F, g, hg, rfl⟩ := mem_weight_sup_exists_finset_sum E (fun _ => True) (htop z)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hw ν _ (hg ν hν).2, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hS _ _ _ (hg ν hν).2, map_smul, map_smul]
    rw [hop, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun ij _ => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    have h1 : S ij.2 x ∈ NablaSub (O := O) E lam v := by
      rw [hSdef, LinearMap.smul_apply]
      exact intCast_smul_mem_submodule _ _ (shifted_binomial_preserves_lattice hN a _ _ hx)
    have h2 : f (S ij.2 x) ∈ Delta (O := O) E v := hf _ h1
    exact hD _ (Or.inr ⟨a, ij.1, rfl⟩) _ h2

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HomLatticeDividedPowerStable
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem homLattice_binomial_stable [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a : Fin n) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    binomE (homRepresentation (restrictRepresentation E L hL) E) a k f ∈ homLattice M L := by
  have hres := restrictRepresentation_isRep E hE L hL
  obtain ⟨s, π, h1, h2, h3, h4, h5⟩ := weight_projections_exist (restrictRepresentation E L hL) hres
  obtain ⟨s', π', h1', h2', h3', h4', h5'⟩ := weight_projections_exist E hE
  have hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have : ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x) := by
      intro mu' _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_sum, h5]
    rw [Finset.sum_congr rfl this, h5']
  have hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu) := by
    intro mu' mu
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul,
      Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]
  have hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype := by
    intro mu
    refine linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_
    have hy' : (y : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu y).1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    by_cases h : nu = mu
    · subst h; rw [(h1 nu).1 y hy, (h1' nu).1 _ hy']
    · rw [(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']; rfl
  have hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L := by
    intro mu' mu x hx
    have hx1 : ((π mu x : L) : W) ∈ M := by
      have := congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]
      exact weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx
    exact weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  refine Submodule.sum_mem _ fun mu' _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Submodule.sum_mem _ fun mu _ => ?_
  rw [binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]
  exact int_smul_mem_lattice _ _ (hmem mu' mu)

theorem mem_homLattice_iff_basis (M : Submodule O W) (L : Submodule (KK O) W) {d : ℕ} (b : Module.Basis (Fin d) (KK O) L)
    (hbM : ∀ i, ((b i : L) : W) ∈ M)
    (hbc : ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o) (f : L →ₗ[KK O] W) :
    f ∈ homLattice M L ↔ ∀ i, f (b i) ∈ M := by
  constructor
  · intro hf i
    exact hf (b i) (hbM i)
  · intro hf
    show ∀ x : L, (x : W) ∈ M → f x ∈ M
    intro x hx
    choose o ho using hbc x hx
    have hx' : x = ∑ i, b.coord i x • b i := by
      simp only [Module.Basis.coord_apply]
      exact (b.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, ho i, algebraMap_smul]
    exact M.smul_mem (o i) (hf i)

end lat

theorem hom_lattice_dividedPower_stable : HomLatticeDividedPowerStable := by
  intro O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL
  obtain ⟨d, b, hbM, hbc⟩ := lattice_adapted_basis_exists O W M hM.2 hMQ L
  have hiff := mem_homLattice_iff_basis M L b hbM hbc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf
    · exact homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf
    · exact homLattice_binomial_stable E hE M hM.1 L hL a k f hf
  · have : homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map
        ((b.constr (KK O)).toLinearMap.restrictScalars O) := by
      ext f
      rw [hiff]
      constructor
      · intro hf
        exact ⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩
      · rintro ⟨y, hy, rfl⟩ i
        have : (b.constr (KK O) y) (b i) = y i := b.constr_basis (KK O) y i
        simpa [this] using hy i trivial
    rw [this]
    exact (Submodule.fg_pi fun _ => hM.2).map _
  · rw [eq_top_iff]
    intro f _
    choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)
    have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
    have hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne hA
    have h1 : (∏ i, a i) • f ∈ homLattice M L := by
      rw [hiff]
      intro i
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
      rw [LinearMap.smul_apply, hc, mul_comm, mul_smul]
      exact M.smul_mem _ (hax i)
    have h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f) := by
      rw [← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionDenominatorBound
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ExtremalProjectorProperties {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (L : ℕ) : Prop :=
  ∀ (c : Fin n) (u : V), u ∈ weightSp E 0 → (∀ a b : Fin n, a < c → b < c → E a b u = 0) →
    (∀ j, j < c → E j c (extremalProjector E c L u) = 0) ∧
    (∀ a b : Fin n, a < c → b < c → E a b (extremalProjector E c L u) = 0) ∧
    extremalProjector E c L u ∈ weightSp E 0 ∧
    ∃ w : Fin n → V, extremalProjector E c L u = u + ∑ i ∈ Finset.Iio c, E c i (w i)

theorem denominator_chain_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x0 : V) (hx0 : x0 ∈ weightSp E 0) (hxM : x0 ∈ M) (c : ℕ) (hc : c ≤ n) :
    ∃ y, y ∈ weightSp E 0 ∧ (∀ a b : Fin n, a.val < c → b.val < c → E a b y = 0) ∧ Inv y = Inv x0 ∧
      ((p : O) ^ ((∑ i ∈ range c, i) * de)) • y ∈ M := by
  induction c with
  | zero =>
    refine ⟨x0, hx0, fun a b ha _ => absurd ha (Nat.not_lt_zero _), rfl, ?_⟩
    simpa using hxM
  | succ c ih =>
    obtain ⟨y, hy0, hyk, hyI, hyM⟩ := ih (Nat.le_of_succ_le hc)
    have hcn : c < n := hc
    obtain ⟨cf, hcf⟩ : ∃ cf : Fin n, cf.val = c := ⟨⟨c, hcn⟩, rfl⟩
    obtain ⟨hA1, hA2, hA3, w, hw⟩ := hA cf y hy0 (fun a b ha hb =>
      hyk a b (by have := Fin.lt_def.mp ha; omega) (by have := Fin.lt_def.mp hb; omega))
    refine ⟨extremalProjector E cf L y, hA3, ?_, ?_, ?_⟩
    · intro a b ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | ha' <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
      · exact hA2 a b (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))
      · have hb2 : b = cf := Fin.ext (by omega)
        subst hb2
        exact hA1 a (Fin.lt_def.mpr (by omega))
      · have ha2 : a = cf := Fin.ext (by omega)
        subst ha2
        exact weight_zero_lowering_kills_raising hE hA3 b a (by rintro rfl; omega) (hA1 b (Fin.lt_def.mpr (by omega)))
      · have ha2 : a = cf := Fin.ext (by omega)
        have hb2 : b = cf := Fin.ext (by omega)
        rw [ha2, hb2]
        have h0 := hA3
        simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at h0
        simpa using h0 cf
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hw, map_add (f := _), map_sum]
      simp only [invariant_projection_kills_operator D h2 E hE Inv hInv, Finset.sum_const_zero, add_zero]
      exact hyI
    · have hM2 := hB cf _ hyM
      rw [LinearMap.map_smul_of_tower, smul_smul, ← pow_add] at hM2
      have he : (∑ i ∈ range (c + 1), i) * de = cf.val * de + (∑ i ∈ range c, i) * de := by
        rw [Finset.sum_range_succ, hcf]; ring
      rw [he]
      exact hM2

theorem invariant_projection_denominator_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero (KK O)] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V]
    (E : GLOps n (KK O) V) (hE : IsGLRep E) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (Inv : Module.End (KK O) V) (hInv : IsInvProj E Inv) (L de : ℕ) (hA : ExtremalProjectorProperties E L)
    (hB : ∀ (c : Fin n) (y : V), y ∈ M → ((p : O) ^ (c.val * de)) • extremalProjector E c L y ∈ M)
    (x : V) (hx : x ∈ M) : ((p : O) ^ (N0 n * de)) • Inv x ∈ M := by
  obtain ⟨Θ, hΘ1, hΘ2⟩ := weight_projections_integral_findim E
  obtain ⟨y, hy0, hyk, hyI, hyM⟩ := denominator_chain_bound D h2 p O n V E hE M Inv hInv L de hA hB (Θ 0 x)
    (weight_projection_mem_weightSpace E hE Θ hΘ2 0 x) (binomial_subring_preserves_lattice hM _ (hΘ1 0) x hx) n le_rfl
  have hInvy : Inv y = y := by
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · apply hInv.1
      exact Submodule.subset_span ⟨1, one_mem _, y, ⟨hy, hy0, fun a b _ => hyk a b a.2 b.2⟩, rfl⟩
  rw [invariant_projection_through_zero_weight D h2 E hE Inv hInv Θ hΘ2 x, ← hyI, hInvy]
  rwa [Finset.sum_range_id] at hyM

end Formalism.MainNotions.G.GLWeightTheory
end
end

