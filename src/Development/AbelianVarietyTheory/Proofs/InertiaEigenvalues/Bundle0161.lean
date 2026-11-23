module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.AutomorphicForms.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import GroundTheory.LocalFields.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.VirtualTrace

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def listSum (h : IsPlaceOver A w) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  L.foldr (fun x s => WD.std (x.2.sum s.2)) ⟨0, WDRep.diag h (ι := Fin 0) fun i => i.elim0⟩

theorem mk_listSum_cons (x : Σ n : ℕ, WDRep h (Fin n → ℂ)) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    WD.mk (listSum h (x :: L)).2 = WD.lpSum (WD.mk x.2) (WD.mk (listSum h L).2) := by
  rw [WD.lpSum_mk]
  exact WD.sound (WD.iso_std _).symm

theorem trace_std {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _

theorem trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']

theorem map_lpZero {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) : f (WD.lpZero (h := h)) = 1 := by
  have hzero := hf (WD.lpZero (h := h)) (WD.lpZero (h := h))
  rw [WD.lpSum_zero] at hzero
  exact mul_left_cancel (hzero.symm.trans (mul_one _).symm)

theorem map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by
  induction L with
  | nil => exact map_lpZero f hf
  | cons x L ih => rw [mk_listSum_cons, hf, ih, List.map_cons, List.prod_cons]

theorem prod_flatMap_replicate {ι α M : Type} [CommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).prod = ∏ i ∈ s, g (x i) ^ n i := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).prod =
      (l.map fun i => g (x i) ^ n i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_replicate, List.prod_replicate]
  rw [key, Finset.prod_map_toList]

theorem sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).sum =
      (l.map fun i => n i • g (x i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih, List.map_replicate, List.sum_replicate]
  rw [key, Finset.sum_map_toList]

end GlobalTheory.WeilDeligne.VirtualTrace


open GlobalTheory.WeilDeligne.VirtualTrace in
theorem GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ),
    (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) →
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ),
    (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) →
    ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  intro E Ω _ _ _ _ _ A w h f hf1 hf2 ι _ d a c hc
  classical
  let x : ι → Σ n : ℕ, WDRep h (Fin n → ℂ) := fun i => ⟨d i, a i⟩
  let L : (ι → ℕ) → List (Σ n : ℕ, WDRep h (Fin n → ℂ)) := fun n =>
    (Finset.univ : Finset ι).toList.flatMap fun i => List.replicate (n i) (x i)
  have hfL : ∀ n, f (WD.mk (listSum h (L n)).2) = ∏ i, f (WD.mk (a i)) ^ n i := fun n => by
    rw [map_listSum f hf1]
    exact prod_flatMap_replicate _ n x (fun y => f (WD.mk y.2))
  have htL : ∀ n σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L n)).2.ρ σ ^ k) =
      ∑ i, (n i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ ^ k) := fun n σ k => by
    rw [trace_listSum]
    rw [sum_flatMap_replicate _ n x (fun y => LinearMap.trace ℂ _ (y.2.ρ σ ^ k))]
    simp only [nsmul_eq_mul, x]
  have hcc : ∀ i, ((c i : ℤ) : ℂ) = (((c i).toNat : ℕ) : ℂ) - (((-c i).toNat : ℕ) : ℂ) := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    push_cast; ring
  have htr : ∀ σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L fun i => (c i).toNat)).2.ρ σ ^ k) =
      LinearMap.trace ℂ _ ((listSum h (L fun i => (-c i).toNat)).2.ρ σ ^ k) := fun σ k => by
    rw [htL, htL, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have := hc (σ ^ k)
    simp only [map_pow, hcc] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPQ : f (WD.mk (listSum h (L fun i => (c i).toNat)).2) =
      f (WD.mk (listSum h (L fun i => (-c i).toNat)).2) :=
    hf2 _ _ fun σ => by
      rw [WD.charPol_mk, WD.charPol_mk]
      exact _root_.GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq _ _ _ _ (htr σ)
  rw [hfL, hfL] at hPQ
  have hz : ∀ i, f (WD.mk (a i)) ^ c i =
      f (WD.mk (a i)) ^ (c i).toNat * (f (WD.mk (a i)) ^ (-c i).toNat)⁻¹ := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hPQ, mul_inv_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardFibreStableLatticePairProjection
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Fibre

variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

theorem inf_ker_snd_eq (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    Submodule.mem_comap, LinearMap.inl_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hx, rfl⟩

theorem isLat_of_comap_inl_map_snd {M : Submodule O (A₁ × A₂)}
    (h₁ : IsLat O E (M.comap (LinearMap.inl O A₁ A₂)))
    (h₂ : IsLat O E (M.map (LinearMap.snd O A₁ A₂))) : IsLat O E M := by
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd O A₁ A₂) h₂.1 ?_, ?_⟩
  · rw [inf_ker_snd_eq]; exact h₁.1.map _
  · set S := Submodule.span E (M : Set (A₁ × A₂)) with hS
    have hl : LinearMap.range (LinearMap.inl E A₁ A₂) ≤ S := by
      rw [LinearMap.range_eq_map, ← h₁.2, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (by simpa using hx)
    have hr : S.map (LinearMap.snd E A₁ A₂) = ⊤ := by
      rw [hS, Submodule.map_span, ← h₂.2]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd E A₁ A₂) := by rw [hr]; trivial
    obtain ⟨z, hz, hzb⟩ := hb
    have hab : ((a, b) : A₁ × A₂) = z + LinearMap.inl E A₁ A₂ (a - z.1) := by
      ext <;> simp [← hzb]
    rw [hab]
    exact S.add_mem hz (hl ⟨_, rfl⟩)

end Fibre

theorem ncard_fibre_latProj (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) :
    resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 →
      ∀ y : LatPair O E g₁ g₂, ((latProj O E g₁ g₂ ⁻¹' {y}).ncard : ℚ) =
        (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^
          val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  intro hR y
  have key := _root_.GlobalTheory.StableLatCount.card_stable_lattices O E A₁ A₂ g₁ g₂ hR y.1.1 y.2.1 y.1.2.1 y.2.2.1 y.1.2.2 y.2.2.2
  let e : ↥(latProj O E g₁ g₂ ⁻¹' {y}) ≃
      {M : Submodule O (A₁ × A₂) // (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧ M.map (LinearMap.snd O A₁ A₂) = y.2.1} :=
    { toFun := fun M => ⟨M.1.1, M.1.2.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.1 : Submodule O A₁)) M.2,
        congrArg (fun p : LatPair O E g₁ g₂ => (p.2 : Submodule O A₂)) M.2⟩
      invFun := fun M => ⟨⟨M.1, isLat_of_comap_inl_map_snd (by rw [M.2.2.1]; exact y.1.2.1)
          (by rw [M.2.2.2]; exact y.2.2.1), M.2.1⟩,
        Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext M.2.2.1) (Subtype.ext M.2.2.2))⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  have hc : (latProj O E g₁ g₂ ⁻¹' {y}).ncard = Nat.card {M : Submodule O (A₁ × A₂) //
      (∀ z ∈ M, (g₁, g₂) * z ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = y.1.1 ∧
        M.map (LinearMap.snd O A₁ A₂) = y.2.1} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  rw [hc]
  exact key

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDivLocalEmbeddingCloseToOne
section
noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory.NormCompat.RatioClose

theorem norm_one_tmul' {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' σ hσ hv M
  classical
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' w M
  refine ⟨M₁, fun z hz0 hz => ?_⟩
  set K := w.adicCompletion E
  let σA : E' →ₐ[E] K := { σ with commutes' := hσ }
  let ψ : K ⊗[E] E' →ₐ[K] K := Algebra.TensorProduct.lift (Algebra.ofId K K) σA (fun _ _ => Commute.all _ _)
  have hψ : ∀ x : E', ψ ((1 : K) ⊗ₜ x) = σ x := fun x => by
    simp [ψ, σA, Algebra.TensorProduct.lift_tmul]
  obtain ⟨e, he1, he⟩ := _root_.GlobalTheory.exists_tensor_idem_of_algHom E K E' ψ
  have hee : e * e = e := by rw [he, he1, map_one, one_mul]
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 E) E E'
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  have hvK : ∀ x : E, Valued.v (algebraMap E K x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hβ : ∀ x : E', x ≠ 0 → algebraMap E K (Algebra.norm E x) / σ x =
      Algebra.norm K (e + (1 - e) * ((1 : K) ⊗ₜ x)) := by
    intro x hx
    have h2 := _root_.GlobalTheory.norm_eq_mul_norm_idem_corner K (K ⊗[E] E') ψ e he1 he ((1 : K) ⊗ₜ x)
    rw [norm_one_tmul', hψ] at h2
    rw [h2, mul_div_cancel_left₀ _ ((map_ne_zero σ).2 hx)]
  let Z : K ⊗[E] E' := (1 : K) ⊗ₜ z
  set p : K ⊗[E] E' := e + (1 - e) * Z with hp
  set q : K ⊗[E] E' := (1 - e) * (1 - Z) with hq
  obtain ⟨K₀, hK₂, hK₁, hK₃⟩ : ∃ K₀ : ℕ, M ≤ K₀ ∧ M₁ ≤ K₀ ∧ 1 ≤ K₀ := ⟨M + M₁ + 1, by omega, by omega, by omega⟩
  set m : ℤ := (w'.valuation E' (z - 1)).log with hm
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, M ≤ n ∧ (K₀ : ℤ) + m ≤ n := ⟨M + K₀ + m.toNat, by omega, by omega⟩
  obtain ⟨ε, hε1, hε2, hε3⟩ := GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion E E' w b ψ e hee he1 p q n
  set y : E' := ε + (1 - ε) * z with hy
  have hy1 : y - 1 = (1 - ε) * (z - 1) := by rw [hy]; ring
  have hw'ε : w'.valuation E' (ε - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hv, map_sub, map_one, ← hψ]; exact hε2
  have hw'y : w'.valuation E' (y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [hy1, map_mul, Valuation.map_sub_swap]
    by_cases hz1 : w'.valuation E' (z - 1) = 0
    · rw [hz1, mul_zero]; exact zero_le'
    calc w'.valuation E' (ε - 1) * w'.valuation E' (z - 1)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp m := by
          rw [hm, WithZero.exp_log hz1]; exact mul_le_mul' hw'ε le_rfl
      _ = WithZero.exp (-(n : ℤ) + m) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(K₀ : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
  have hall : ∀ w'' : HeightOneSpectrum (𝓞 E'), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal →
      w''.valuation E' (y - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
    intro w'' h1
    by_cases h2 : w'' = w'
    · subst h2
      exact hw'y.trans (WithZero.exp_le_exp.2 (by omega))
    rw [hy1, map_mul]
    have hi := GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis E E' b hb' w w'' h1 ε hε1
    have h1e : w''.valuation E' (1 - ε) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (by simp) hi)
    calc w''.valuation E' (1 - ε) * w''.valuation E' (z - 1) ≤ 1 * WithZero.exp (-(M₁ : ℤ)) :=
          mul_le_mul' h1e (hz w'' h1 h2)
      _ = _ := one_mul _
  have hN := hM₁ y hall
  have hσy : Valued.v (σ y - 1) ≤ WithZero.exp (-(K₀ : ℤ)) := by
    rw [← map_one σ, ← map_sub, hv]; exact hw'y
  have hσy1 : Valued.v (σ y) = 1 := by
    have hlt : Valued.v (σ y - 1) < Valued.v (1 : K) := by
      rw [map_one]
      refine hσy.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
  have hσy0 : σ y ≠ 0 := fun h => by rw [h, map_zero] at hσy1; exact zero_ne_one hσy1
  have hy0 : y ≠ 0 := fun h => hσy0 (by rw [h, map_zero])
  have hry : Valued.v (algebraMap E K (Algebra.norm E y) / σ y - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [div_sub_one hσy0, map_div₀, hσy1, div_one]
    have : algebraMap E K (Algebra.norm E y) - σ y =
        (algebraMap E K (Algebra.norm E y) - 1) - (σ y - 1) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hσy.trans (WithZero.exp_le_exp.2 (by omega))))
    rw [← map_one (algebraMap E K), ← map_sub, hvK]; exact hN
  have hid : e + (1 - e) * ((1 : K) ⊗ₜ y) = p + q * ((1 : K) ⊗ₜ ε - e) := by
    have h1 : (1 : K) ⊗ₜ[E] y = (1 : K) ⊗ₜ ε + (1 - (1 : K) ⊗ₜ ε) * Z := by
      have := map_add (Algebra.TensorProduct.includeRight (R := E) (A := K) (B := E')) ε ((1 - ε) * z)
      simp only [Algebra.TensorProduct.includeRight_apply, map_mul, map_sub, map_one] at this
      rw [hy, this]
    rw [h1, hp, hq]
    linear_combination (Z - 1) * hee
  have hbz := hβ z hz0
  have hby : algebraMap E K (Algebra.norm E y) / σ y = Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) := by
    rw [hβ y hy0, hid]
  rw [hbz]
  have : Algebra.norm K p - 1 = (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - 1) -
      (Algebra.norm K (p + q * ((1 : K) ⊗ₜ ε - e)) - Algebra.norm K p) := by ring
  rw [this]
  refine (Valuation.map_sub _ _ _).trans (max_le (hby ▸ hry) (hε3.trans (WithZero.exp_le_exp.2 ?_)))
  omega

end GlobalTheory.NormCompat.RatioClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne
section
open scoped TensorProduct

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.NormSign

theorem exists_valuativeRel_of_normed : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F],
    ∃ _ : ValuativeRel F, IsNonarchimedeanLocalField F ∧ ∀ x y : F, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  intro F _ _ _
  letI rel : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  have hc : (NormedField.valuation (K := F)).Compatible := Valuation.Compatible.ofValuation _
  refine ⟨rel, ?_, fun x y => Iff.rfl⟩
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := inferInstance, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := F))
      (fun {s} => (NormedField.toValued (K := F)).is_topological_valuation s)
  · rw [ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))]
    infer_instance

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem norm_algebraMap_of_isPushout : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]

theorem mul_norm_of_not_norm (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (s t : Kˣ) (hs : ¬ ∃ y : L, Algebra.norm K y = s) (ht : ¬ ∃ y : L, Algebra.norm K y = t) :
    ∃ y : L, Algebra.norm K y = ((s * t : Kˣ) : K) := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hN := GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two (F := K) (E := L)
  have ht' : t ∉ (GroundTheory.LocalField.normUnits K L).range := fun h =>
    ht ((GroundTheory.Automorphic.mem_range_normUnits_iff t).1 h)
  rcases GroundTheory.Automorphic.mem_or_mul_inv_mem_of_natCard_eq_two hN ht' s with h | h
  · exact absurd ((GroundTheory.Automorphic.mem_range_normUnits_iff s).1 h) hs
  · obtain ⟨z, hz⟩ := (GroundTheory.Automorphic.mem_range_normUnits_iff _).1 h
    refine ⟨z * algebraMap K L (t : K), ?_⟩
    rw [map_mul, hz, Algebra.norm_algebraMap, h2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := t.ne_zero
    field_simp

theorem norms_of_isField {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨by
      intro a b
      rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.neg_one_mem_norm_of_valuation_eq F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]

theorem omega_mul_neg_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → (∀ s t : A.Kˣ, ω ((s * t : A.Kˣ) : A.K) = ω s * ω t) ∧ ω ((-1 : A.Kˣ) : A.K) = 1 := by
  classical
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, -, -, hω⟩ := h
  obtain ⟨hzero, hprod, hneg⟩ := norms_of_isField A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  have hmul : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y * y', by simp only [Et.NL] at hy hy' ⊢; rw [map_mul, hy, hy', Units.val_mul]⟩
  have hdiv : ∀ s t : A.Kˣ, (∃ y, A.NL y = s) → (∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) → ∃ y, A.NL y = t := by
    rintro s t ⟨y, hy⟩ ⟨y', hy'⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [hzero] at hy
      exact s.ne_zero hy.symm
    refine ⟨y' * y⁻¹, ?_⟩
    have h1 : A.NL y * A.NL y⁻¹ = 1 := by
      simp only [Et.NL]; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    simp only [Et.NL] at hy hy' h1 ⊢
    rw [map_mul, hy', Units.val_mul]
    rw [hy] at h1
    calc (s : A.K) * t * (Algebra.norm A.K) y⁻¹ = t * ((s : A.K) * (Algebra.norm A.K) y⁻¹) := by ring
      _ = t := by rw [h1, mul_one]
  have hval : ∀ s : A.Kˣ, ω s = if ∃ y, A.NL y = s then 1 else -1 := by
    intro s
    split_ifs with hs
    · exact (hω s).1 hs
    · exact (hω s).2 hs
  refine ⟨fun s t => ?_, by rw [hval, if_pos hneg]⟩
  rw [hval s, hval t, hval (s * t)]
  by_cases hs : ∃ y, A.NL y = s <;> by_cases ht : ∃ y, A.NL y = t
  · rw [if_pos hs, if_pos ht, if_pos (hmul s t hs ht)]; ring
  · rw [if_pos hs, if_neg ht, if_neg (fun h => ht (hdiv s t hs h))]; ring
  · have hst : ¬ ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K) := fun h => hs (hdiv t s ht (by rwa [mul_comm]))
    rw [if_neg hs, if_pos ht, if_neg hst]; ring
  · rw [if_neg hs, if_neg ht, if_pos (hprod s t hs ht)]; ring

end GlobalTheory.JR.WeilQuad.NormSign
end
end

