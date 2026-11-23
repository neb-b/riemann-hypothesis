module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZero
section
open scoped TensorProduct

namespace GlobalTheory


open MvPolynomial in
theorem exists_field_combination_norm_ne_zero {k B A : Type} [Field k] [Infinite k] [CommRing B]
    [IsDomain B] [Algebra k B] [CommRing A] [Algebra B A] [Module.Free B A] [Module.Finite B A]
    {d : ℕ} (y : Fin d → A) (hx : ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) :
    ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx
  let b := Module.Free.chooseBasis B A
  let M : Matrix (Module.Free.ChooseBasisIndex B A) (Module.Free.ChooseBasisIndex B A)
      (MvPolynomial (Fin d) B) :=
    Matrix.of fun j l => ∑ i, X i * C (Algebra.leftMulMatrix b (y i) j l)
  have heval : ∀ x : Fin d → B, eval x M.det = Algebra.norm B (∑ i, x i • y i) := by
    intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [M, map_sum, Matrix.sum_apply, mul_comm]
  by_contra hcon
  push_neg at hcon
  have hinf : ∀ _ : Fin d, (Set.range (algebraMap k B)).Infinite := fun _ =>
    Set.infinite_range_of_injective (algebraMap k B).injective
  have hQ : M.det = 0 := by
    refine funext_set (fun _ => Set.range (algebraMap k B)) hinf fun x hx => ?_
    choose a ha using fun i => hx i (Set.mem_univ i)
    rw [heval, map_zero, ← hcon a]
    simp [ha]
  exact hx₀ (by rw [← heval, hQ, map_zero])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningFunctional
section
universe u_1 u_2 u_3

namespace GlobalTheory.IntertwiningFunctional

private theorem freeAlgebra_lift_intertwine {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V) (T : V →ₗ[ℂ] F)
    (hT : ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) (a : FreeAlgebra ℂ K) :
    ∀ v : V, T (FreeAlgebra.lift ℂ ρ a v) = FreeAlgebra.lift ℂ r a (T v) := by
  induction a using FreeAlgebra.induction with
  | grade0 c => intro v; simp [AlgHom.commutes, Module.algebraMap_end_apply]
  | grade1 k => intro v; simp [FreeAlgebra.lift_ι_apply, hT]
  | mul a b ha hb => intro v; simp only [map_mul, Module.End.mul_apply]; rw [ha, hb]
  | add a b ha hb => intro v; simp only [map_add (f := _), LinearMap.add_apply]; rw [ha, hb]

theorem exists_intertwining_functional {K : Type u_1} {F : Type u_2} {V : Type u_3}
    [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ (W : Submodule ℂ V), (∀ (k : K), ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop)
    (hP : ∀ (T : V →ₗ[ℂ] F), P T → ∀ (k : K) (v : V), T (ρ k v) = r k (T v)) :
    ∀ f ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T, f ≠ (0 : F) →
      ∃ (φ : F →ₗ[ℂ] V), φ f ≠ (0 : V) ∧ ∀ (k : K),
        ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T,
          φ (r k f') = ρ k (φ f') := by
  classical
  intro f hf hf0
  set S := ⨆ (T : V →ₗ[ℂ] F), ⨆ (_ : P T), LinearMap.range T with hSdef

  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    apply hf0
    have hS : S = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun T _ => ?_)
      rintro _ ⟨v, rfl⟩
      rw [Subsingleton.elim v 0, map_zero]
      exact Submodule.zero_mem _
    rw [hS, Submodule.mem_bot] at hf
    exact hf

  let A := FreeAlgebra ℂ K
  let rA : A →ₐ[ℂ] Module.End ℂ F := FreeAlgebra.lift ℂ r
  let ρA : A →ₐ[ℂ] Module.End ℂ V := FreeAlgebra.lift ℂ ρ
  let : Module A F := Module.compHom F rA.toRingHom
  let : Module A V := Module.compHom V ρA.toRingHom
  have smulF : ∀ (a : A) (x : F), a • x = rA a x := fun _ _ => rfl
  have smulV : ∀ (a : A) (x : V), a • x = ρA a x := fun _ _ => rfl
  have : IsScalarTower ℂ A F := ⟨fun c a x => by
    rw [smulF, smulF, map_smul, LinearMap.smul_apply]⟩
  have : IsScalarTower ℂ A V := ⟨fun c a x => by
    rw [smulV, smulV, map_smul, LinearMap.smul_apply]⟩
  have hιF : ∀ (k : K) (x : F), (FreeAlgebra.ι ℂ k : A) • x = r k x := fun k x => by
    show FreeAlgebra.lift ℂ r (FreeAlgebra.ι ℂ k) x = r k x
    rw [FreeAlgebra.lift_ι_apply]
  have hιV : ∀ (k : K) (v : V), (FreeAlgebra.ι ℂ k : A) • v = ρ k v := fun k v => by
    show FreeAlgebra.lift ℂ ρ (FreeAlgebra.ι ℂ k) v = ρ k v
    rw [FreeAlgebra.lift_ι_apply]

  have hVs : IsSimpleModule A V := by
    refine { toNontrivial := inferInstance, eq_bot_or_eq_top := fun W => ?_ }
    have hWinv : ∀ (k : K), ∀ v ∈ W.restrictScalars ℂ, ρ k v ∈ W.restrictScalars ℂ := by
      intro k v hv
      rw [← hιV]
      exact W.smul_mem _ hv
    rcases hirr (W.restrictScalars ℂ) hWinv with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

  let mkA : ∀ T : V →ₗ[ℂ] F, (∀ (k : K) (v : V), T (ρ k v) = r k (T v)) → V →ₗ[A] F :=
    fun T hT =>
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun a v => freeAlgebra_lift_intertwine r ρ T hT a v }
  let p : (V →ₗ[ℂ] F) → Submodule A F := fun T =>
    if h : ∀ (k : K) (v : V), T (ρ k v) = r k (T v) then LinearMap.range (mkA T h) else ⊥
  let s : Set (V →ₗ[ℂ] F) := {T | P T}
  let SA : Submodule A F := ⨆ T ∈ s, p T
  have hpT : ∀ T (hT : T ∈ s), p T = LinearMap.range (mkA T (hP T hT)) :=
    fun T hT => dif_pos (hP T hT)
  have hpSA : ∀ T (hT : T ∈ s), p T ≤ SA := fun T hT =>
    le_iSup₂ (f := fun T (_ : T ∈ s) => p T) T hT
  have memSA : ∀ x : F, x ∈ S ↔ x ∈ SA := by
    intro x
    constructor
    · intro hx
      have hle : S ≤ SA.restrictScalars ℂ := by
        refine iSup₂_le fun T hT => ?_
        rintro _ ⟨v, rfl⟩
        have h1 : T v ∈ p T := by
          rw [hpT T hT]
          exact ⟨v, rfl⟩
        exact hpSA T hT h1
      exact hle hx
    · intro hx
      refine Submodule.iSup_induction (fun T => ⨆ (_ : T ∈ s), p T) (motive := fun y => y ∈ S)
        hx ?_ (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _)
      intro T y hy
      by_cases hT : T ∈ s
      · have hy' : y ∈ p T := (iSup_le fun _ => le_rfl : (⨆ (_ : T ∈ s), p T) ≤ p T) hy
        rw [hpT T hT] at hy'
        obtain ⟨v, rfl⟩ := hy'
        exact (le_iSup₂ (f := fun T (_ : P T) => LinearMap.range T) T hT : _ ≤ S) ⟨v, rfl⟩
      · rw [iSup_neg hT, Submodule.mem_bot] at hy
        rw [hy]
        exact Submodule.zero_mem _

  have : IsSemisimpleModule A SA :=
    isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (fun T hT => by
      rw [hpT T hT]
      exact IsSemisimpleModule.range _)
  let f₀ : SA := ⟨f, (memSA f).mp hf⟩
  have hf₀ : f₀ ≠ 0 := fun h => hf0 (congrArg Subtype.val h)

  obtain ⟨m, hmN, hm⟩ : ∃ m ≤ Submodule.span A {f₀}, IsSimpleModule A m := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (Submodule.span A {f₀}) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hf₀
    · exact h
  have := hm
  have : Nontrivial m := IsSimpleModule.nontrivial A m
  obtain ⟨q, hq⟩ := exists_isCompl m
  let π : SA →ₗ[A] m := Submodule.projectionOnto m q hq
  have hπleft : ∀ y : m, π y = y := fun y => Submodule.projectionOnto_apply_left hq y
  have hπf : π f₀ ≠ 0 := by
    intro h0
    have hNk : Submodule.span A {f₀} ≤ LinearMap.ker π := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h0
    obtain ⟨y, hy0⟩ := exists_ne (0 : m)
    apply hy0
    have hyk : (y : SA) ∈ LinearMap.ker π := hNk (hmN y.2)
    rw [LinearMap.mem_ker, hπleft] at hyk
    exact hyk

  have hmemT : ∀ T (hT : T ∈ s) (v : V), mkA T (hP T hT) v ∈ SA := fun T hT v =>
    hpSA T hT (by rw [hpT T hT]; exact ⟨v, rfl⟩)
  obtain ⟨T, hT, hg⟩ : ∃ T, ∃ hT : T ∈ s,
      π ∘ₗ LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hπf
    have hle : SA ≤ (LinearMap.ker π).map SA.subtype := by
      refine iSup₂_le fun T hT => ?_
      rw [hpT T hT]
      rintro _ ⟨v, rfl⟩
      refine ⟨LinearMap.codRestrict SA (mkA T (hP T hT)) (hmemT T hT) v, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, hne T hT, LinearMap.zero_apply]
    obtain ⟨y, hy, hyf⟩ := hle f₀.2
    have hyeq : y = f₀ := Subtype.ext hyf
    rw [← hyeq]
    exact hy
  let e : V ≃ₗ[A] m := LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hg)
  let φ₀ : SA →ₗ[A] V := e.symm.toLinearMap ∘ₗ π
  have hφ₀f : φ₀ f₀ ≠ 0 := by
    intro h
    apply hπf
    have h1 : e (φ₀ f₀) = π f₀ := e.apply_symm_apply (π f₀)
    rw [← h1, h, map_zero]

  let ψ : S →ₗ[ℂ] V :=
    { toFun := fun x => φ₀ ⟨x.1, (memSA x.1).mp x.2⟩
      map_add' := fun x y => by
        rw [← map_add (f := _)]
        rfl
      map_smul' := fun c x => by
        have h1 : (⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ : SA) =
            algebraMap ℂ A c • (⟨x.1, (memSA _).mp x.2⟩ : SA) :=
          Subtype.ext (algebraMap_smul (A := A) c x.1).symm
        show φ₀ ⟨c • x.1, (memSA _).mp (S.smul_mem c x.2)⟩ = c • φ₀ ⟨x.1, (memSA _).mp x.2⟩
        rw [h1, map_smul, algebraMap_smul] }
  obtain ⟨φ, hφext⟩ := LinearMap.exists_extend ψ
  have hφ : ∀ (x : F) (hx : x ∈ S), φ x = φ₀ ⟨x, (memSA x).mp hx⟩ := fun x hx =>
    LinearMap.congr_fun hφext ⟨x, hx⟩
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ f hf]
    exact hφ₀f
  · intro k x hx
    have hrk : r k x = (FreeAlgebra.ι ℂ k : A) • x := (hιF k x).symm
    have hmem : r k x ∈ S := by
      rw [memSA, hrk]
      exact SA.smul_mem _ ((memSA _).mp hx)
    rw [hφ _ hmem, hφ _ hx, ← hιV k, ← map_smul φ₀]
    congr 1
    exact Subtype.ext hrk

end GlobalTheory.IntertwiningFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowValuationDivSubOneLeOfCongr
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_pow_valuation_div_sub_one_le :
    ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 →
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N →
        v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  intro E _ _ v c hc n
  set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hval : v.valuation E (c : E) = WithZero.exp (-(e : ℤ)) := by
    have h := HeightOneSpectrum.valuation_of_algebraMap (K := E) v c
    have h' : v.valuation E (c : E) = v.intValuation c := h
    rw [h', v.intValuation_if_neg hc]
  have hcE : (c : E) ≠ 0 := by
    simpa using hc
  refine ⟨n + e, fun k hk => ?_⟩
  have hle : v.intValuation (k - c) ≤ WithZero.exp (-((n + e : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem (k - c) (n + e)).2 hk
  have hdiff : v.valuation E (((k - c : 𝓞 E)) : E) = v.intValuation (k - c) :=
    HeightOneSpectrum.valuation_of_algebraMap (K := E) v (k - c)
  have heq : (k : E) / (c : E) - 1 = (((k - c : 𝓞 E)) : E) / (c : E) := by
    push_cast
    field_simp
  rw [heq, map_div₀, hval, hdiff]
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(e : ℤ)) := WithZero.exp_pos
  rw [div_le_iff₀ hpos, ← WithZero.exp_add]
  have hexp : -(n : ℤ) + -(e : ℤ) = -((n + e : ℕ) : ℤ) := by
    push_cast
    ring
  rwa [hexp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepresent
section
namespace GlobalTheory.ExistsRepresentation

theorem exists_represent {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → (0 : ℝ) < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  classical
  let b := Module.finBasis ℂ W
  let Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => Bf (u : V) (b i : V)
      map_add' := by
        intro u u'
        funext i
        simp
      map_smul' := by
        intro c u
        funext i
        simp }
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ w : W, Bf (u : V) (w : V) = 0 := by
      intro w
      rw [← b.sum_repr w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 := congrFun hu i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      simp [h0]
    by_contra hne
    have hne' : (u : V) ≠ 0 := by simpa using hne
    have h1 := hpos _ hne'
    rw [hall u] at h1
    simp at h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun i => L (b i : V))
  refine ⟨u, u.2, fun w hw => ?_⟩
  have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V) := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  rw [hwsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h3 := congrFun hu i
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3
  rw [h3]

end GlobalTheory.ExistsRepresentation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRepsCoprimeOutsideModulus
section
namespace GlobalTheory


open IsDedekindDomain in
theorem exists_reps_coprime_outside_modulus : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (m : Ideal A) (a₀ b₀ : A), m ≠ ⊥ → ∃ a b : A, a - a₀ ∈ m ∧ b - b₀ ∈ m ∧ b ≠ 0 ∧ ∀ p : Ideal A, p.IsMaximal → ¬ m ≤ p → ¬ (a ∈ p ∧ b ∈ p) := by
  classical
  intro A _ _ m a₀ b₀ hm
  obtain ⟨b, hbm, hb0⟩ : ∃ b, b - b₀ ∈ m ∧ b ≠ 0 := by
    by_cases h : b₀ = 0
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      exact ⟨x, by simpa [h] using hx, hx0⟩
    · exact ⟨b₀, by simp, h⟩
  have hspan : Ideal.span {b} ≠ (0 : Ideal A) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  have hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {b}}.Finite :=
    Ideal.finite_factors hspan
  let S := hfin.toFinset.filter (fun v => ¬ m ≤ v.asIdeal)
  let K : Ideal A := ⨅ v ∈ S, v.asIdeal
  have hK : m ⊔ K = ⊤ := by
    apply Ideal.sup_iInf_eq_top
    intro v hv
    have hv' : ¬ m ≤ v.asIdeal := (Finset.mem_filter.mp hv).2
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    by_contra hne
    rw [sup_comm] at hne
    have heq := hmax.eq_of_le hne le_sup_left
    exact hv' (heq ▸ le_sup_right)
  have h1 : (1 : A) ∈ m ⊔ K := by rw [hK]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  refine ⟨a₀ * y + x, b, ?_, hbm, hb0, ?_⟩
  · have : a₀ * y + x - a₀ = x - a₀ * x := by
      have hy' : y = 1 - x := by rw [← hxy]; ring
      rw [hy']; ring
    rw [this]
    exact m.sub_mem hx (m.mul_mem_left a₀ hx)
  · rintro p hp hmp ⟨hap, hbp⟩
    have hp0 : p ≠ ⊥ := by
      rintro rfl
      exact hb0 ((Submodule.mem_bot A).mp hbp)
    let v : HeightOneSpectrum A := ⟨p, hp.isPrime, hp0⟩
    have hvS : v ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, hmp⟩
      rw [Set.Finite.mem_toFinset]
      show p ∣ Ideal.span {b}
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hbp
    have hKp : K ≤ p := iInf₂_le v hvS
    have hyp : y ∈ p := hKp hy
    have hxp : x ∈ p := by
      have := p.sub_mem hap (p.mul_mem_left a₀ hyp)
      simpa using this
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (hxy ▸ p.add_mem hxp hyp))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsResidueClassNearRealEmbeddings
section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace GlobalTheory

theorem exists_realPlace_embedding {F : Type} [Field F] [NumberField F] (τ : F →+* ℝ) :
    ∃ (P : InfinitePlace F) (hP : P.IsReal), embedding_of_isReal hP = τ := by
  have hreal : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hP : (InfinitePlace.mk (Complex.ofRealHom.comp τ)).IsReal := isReal_mk_iff.2 hreal
  refine ⟨_, hP, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal hreal]
  simp

theorem exists_integer_near (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ w : (F →+* ℝ) → ℝ, ∃ z : 𝓞 F, ∀ τ : F →+* ℝ, |τ (z : F) - w τ| ≤ C := by
  classical
  have hfin : Finite (F →+* ℝ) := by
    refine Finite.of_injective (fun τ => (Complex.ofRealHom.comp τ : F →+* ℂ)) ?_
    intro a b h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this
  have := Fintype.ofFinite (F →+* ℝ)
  let b := RingOfIntegers.basis F
  refine ⟨∑ τ : F →+* ℝ, ∑ i, |τ ((b i : 𝓞 F) : F)|, fun w => ?_⟩
  let v : mixedSpace F := (fun w' => w (embedding_of_isReal w'.2), 0)
  let c := (latticeBasis F).repr v
  refine ⟨∑ i, round (c i) • b i, fun τ => ?_⟩
  obtain ⟨P, hP, hτ⟩ := exists_realPlace_embedding τ
  have hv : v = ∑ i, c i • latticeBasis F i := ((latticeBasis F).sum_repr v).symm
  have hw : w τ = ∑ i, c i * τ ((b i : 𝓞 F) : F) := by
    have h1 := congrArg (fun u : mixedSpace F => u.1 ⟨P, hP⟩) hv
    simp only [v, hτ] at h1
    rw [h1]
    simp [Prod.fst_sum, Finset.sum_apply, latticeBasis_apply, integralBasis_apply,
      mixedEmbedding_apply_isReal, hτ, b, c, v]
  have hz : τ (((∑ i, round (c i) • b i : 𝓞 F)) : F)
      = ∑ i, (round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [hz, hw, ← Finset.sum_sub_distrib]
  calc |∑ i, ((round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F))|
      ≤ ∑ i, |(round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |τ ((b i : 𝓞 F) : F)| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_mul, abs_mul]
        have h2 : |(round (c i) : ℝ) - c i| ≤ 1 := by
          have := abs_sub_round (c i)
          rw [abs_sub_comm]
          linarith
        exact mul_le_of_le_one_left (abs_nonneg _) h2
    _ ≤ ∑ τ' : F →+* ℝ, ∑ i, |τ' ((b i : 𝓞 F) : F)| :=
        Finset.single_le_sum (f := fun τ' : F →+* ℝ => ∑ i, |τ' ((b i : 𝓞 F) : F)|)
          (fun τ' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ τ)

theorem residueClass_relativelyDense : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ →
    ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧
      ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  intro F _ _ _ m a₀ hm
  obtain ⟨C, hC⟩ := exists_integer_near F
  have hMpos : 0 < Ideal.absNorm m := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.1 h))
  set M : ℕ := Ideal.absNorm m with hMdef
  have hMmem : ((M : ℕ) : 𝓞 F) ∈ m := Ideal.absNorm_mem m
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine ⟨M * C, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hC (fun τ => (y τ - τ (a₀ : F)) / M)
  refine ⟨a₀ + (M : 𝓞 F) * z, ?_, fun τ => ?_⟩
  · simpa using m.mul_mem_right z hMmem
  · have h := hz τ
    have h3 : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) - y τ
        = M * (τ (z : F) - (y τ - τ (a₀ : F)) / M) := by
      have : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) = τ (a₀ : F) + M * τ (z : F) := by
        simp
      rw [this]
      field_simp
      ring
    rw [h3, abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_left h hM0.le

end GlobalTheory
end

