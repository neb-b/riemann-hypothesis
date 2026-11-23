module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeRestr
section
open IsLocalRing UpperTheory.V.Hi

private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y : Submodule A M}
    {t : Module.End A Y} {φ : Module.End A M} (h : Restr t φ) (n : ℕ) : Restr (t ^ n) (φ ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem mem_locPart_iff {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {op : ι → Module.End A M} {a : ι → A} (u : ι → Module.End A Y)
    (hu : ∀ i, Restr (u i) (op i - algebraMap A _ (a i))) (y : Y) :
    (y : M) ∈ locPart Y op a ↔
      ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (u i ^ n) y ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) := by
  have hmono : ∀ (i : ι) (k : ℕ), Monotone fun n : ℕ =>
      (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n) := by
    intro i k
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      rw [← hu i ⟨z, hz⟩]
      exact (u i ⟨z, hz⟩).2
    · intro b c hb hc
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hb hc
  unfold locPart
  rw [Submodule.mem_inf, and_iff_right y.2]
  simp only [Submodule.mem_iInf]
  refine forall_congr' fun i => forall_congr' fun k => ?_
  rw [Submodule.mem_iSup_of_directed _ (hmono i k).directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, Submodule.mem_smul_top_iff, restr_pow (hu i) n y]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (j : T →ₐ[A] Module.End A Y) (j' : T' →ₐ[A] Module.End A (locPart Y op a)), Function.Injective j → j.range = heckeAlg Y op → Function.Injective j' → j'.range = heckeAlg (locPart Y op a) op → ∃ r : T →ₐ[A] T', Function.Surjective r ∧ (∀ (s : T) (y : locPart Y op a), (j' (r s) y : M) = j s ⟨y, y.2.1⟩) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : T →+* R), (∀ c ∈ maximalIdeal A, x (algebraMap A T c) ∈ maximalIdeal R) → (∀ i s, Restr (j s) (op i) → x s - x (algebraMap A T (a i)) ∈ maximalIdeal R) → locPart Y op a ≠ ⊥ ∧ ∃ x' : T' →+* R, x'.comp (r : T →+* T') = x := by
  intro A M ι _ _ _ _ Y _ op a hC T T' _ _ _ _ j j' hj hjr hj' hjr'
  have ht0 : ∀ i, ∃ s : T, Restr (j s) (op i) := by
    intro i
    have h : (op i).restrict (hC.1 i) ∈ j.range := by
      rw [hjr]
      exact Algebra.subset_adjoin ⟨i, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun y => ?_⟩
    have hs' : j s = (op i).restrict (hC.1 i) := hs
    rw [hs']
    rfl
  choose t ht using ht0
  have hset : ∀ (Z : Submodule A M) (ρ : T →ₐ[A] Module.End A Z), (∀ i, Restr (ρ (t i)) (op i)) →
      (Algebra.adjoin A (Set.range t)).map ρ = heckeAlg Z op := by
    intro Z ρ hρ
    rw [AlgHom.map_adjoin, heckeAlg]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, hρ i⟩
    · rintro ⟨i, hi⟩
      exact ⟨t i, ⟨i, rfl⟩, LinearMap.ext fun y => Subtype.ext ((hρ i y).trans (hi y).symm)⟩
  have hgen : Algebra.adjoin A (Set.range t) = ⊤ := by
    refine eq_top_iff.2 fun s _ => ?_
    have h : j s ∈ (Algebra.adjoin A (Set.range t)).map j := by
      rw [hset Y j ht, ← hjr]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs', h'⟩ := h
    rwa [← hj h']
  haveI : IsNoetherian A (Module.End A Y) := isNoetherian_linearMap A Y Y
  haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj
  obtain ⟨e, he, hnil, h1e, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a hgen
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    refine Submodule.span_induction (p := fun μ _ => ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)) ?_ ?_ ?_ ?_ hμ
    · rintro _ ⟨c, hc, rfl⟩ y
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro y; simp
    · intro b c _ _ hb hc y
      rw [map_add (f := _), LinearMap.add_apply]
      exact Submodule.add_mem _ (hb y) (hc y)
    · intro b c _ hc y
      rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
      exact hc _
  have hL : ∀ y : Y, (y : M) ∈ locPart Y op a ↔ j e y = y := by
    intro y
    rw [mem_locPart_iff (fun i => j (t i - algebraMap A T (a i)))]
    · exact (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _ _ e hI he hnil h1e y).symm
    · intro i z
      rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, ht i z]
      rfl
  have hpres : ∀ (s : T) (y : locPart Y op a), (j s ⟨y, y.2.1⟩ : M) ∈ locPart Y op a := by
    intro s y
    rw [hL, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
      (hL ⟨y, y.2.1⟩).1 y.2]
  have he' : ∀ y : Y, (j e y : M) ∈ locPart Y op a := by
    intro y
    rw [hL, ← Module.End.mul_apply, ← map_mul, he.eq]
  let ρ0 : T → Module.End A (locPart Y op a) := fun s =>
    LinearMap.codRestrict _ (Y.subtype ∘ₗ j s ∘ₗ Submodule.inclusion inf_le_left) (hpres s)
  have hρ0 : ∀ s y, (ρ0 s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  let ρ : T →ₐ[A] Module.End A (locPart Y op a) :=
    { toFun := ρ0
      map_one' := by ext y; rw [hρ0, map_one]; rfl
      map_mul' := fun s s' => by ext y; rw [hρ0, map_mul]; rfl
      map_zero' := by ext y; rw [hρ0, map_zero]; rfl
      map_add' := fun s s' => by ext y; rw [hρ0, map_add (f := _)]; rfl
      commutes' := fun c => by ext y; rw [hρ0, AlgHom.commutes]; rfl }
  have hρ : ∀ s y, (ρ s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  have hrange : ρ.range = j'.range := by
    rw [hjr', ← hset _ ρ (fun i y => by rw [hρ, ht i]), hgen, Algebra.map_top]
  let r : T →ₐ[A] T' := (AlgEquiv.ofInjective j' hj').symm.toAlgHom.comp
    (ρ.codRestrict j'.range fun s => hrange ▸ ⟨s, rfl⟩)
  have hr : ∀ s, j' (r s) = ρ s := fun s =>
    congrArg Subtype.val ((AlgEquiv.ofInjective j' hj').apply_symm_apply
      (ρ.codRestrict j'.range (fun s => hrange ▸ ⟨s, rfl⟩) s))
  have hsurj : Function.Surjective r := by
    intro s'
    have h : j' s' ∈ ρ.range := hrange ▸ ⟨s', rfl⟩
    obtain ⟨s, hs⟩ := h
    exact ⟨s, hj' ((hr s).trans hs)⟩
  refine ⟨r, hsurj, fun s y => by rw [hr, hρ], fun R _ _ x hx hxt => ?_⟩
  have hle : (maximalIdeal A).map (algebraMap A T) ⊔
      Ideal.span (Set.range fun i => t i - algebraMap A T (a i)) ≤ (maximalIdeal R).comap x := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun c hc => hx c hc) (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    have := hxt i (t i) (ht i)
    rwa [← map_sub] at this
  have hxe : x e = 1 := by
    have h1 : 1 - x e ∈ maximalIdeal R := by
      have := hle h1e
      rwa [Ideal.mem_comap, map_sub, map_one] at this
    have h2 : IsUnit (x e) := by
      have := isUnit_one_sub_self_of_mem_nonunits _ h1
      rwa [sub_sub_cancel] at this
    exact h2.mul_left_cancel (by rw [← map_mul, he.eq, mul_one])
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 : e = 0 := by
      refine hj ?_
      rw [map_zero]
      ext y
      have := he' y
      rw [hb] at this
      exact this
    rw [h0, map_zero] at hxe
    exact zero_ne_one hxe
  · have hker : RingHom.ker (r : T →+* T') ≤ RingHom.ker x := by
      intro s hs
      have hs0 : r s = 0 := hs
      have h0 : s * e = 0 := by
        refine hj ?_
        ext y
        have := hρ s ⟨_, he' y⟩
        rw [← hr, hs0, map_zero] at this
        rw [map_mul, map_zero]
        exact this.symm
      rw [RingHom.mem_ker, ← mul_one (x s), ← hxe, ← map_mul, h0, map_zero]
    exact ⟨(r : T →+* T').liftOfSurjective hsurj ⟨x, hker⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepEigCompl
section
open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section SlopeTestRemainingChoices

variable {k H V : Type} [Field k] [Group H] [AddCommGroup V] [Module k V]

private def ecStab (T : Representation k H V) (v : V) : Subgroup H where
  carrier := {g | T g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

private theorem ec_out (T : Representation k H V) (v : V) (S : Subgroup H) (hS : S ≤ ecStab T v) (g : H) :
    T ((g : H ⧸ S).out) v = T g v := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S g
  have h : T s v = v := hS s.2
  rw [hs, map_mul, Module.End.mul_apply, h]

private theorem ec_right (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    ∑ q : H ⧸ S, T q.out (T n v) = ∑ q : H ⧸ S, T q.out v := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulRight (n : H ⧸ S) q = ((q.out * n : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

private theorem ec_left (T : Representation k H V) (v : V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)]
    (hS : S ≤ ecStab T v) (n : H) :
    T n (∑ q : H ⧸ S, T q.out v) = ∑ q : H ⧸ S, T q.out v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (n : H ⧸ S)) _ _ fun q => ?_
  have : Equiv.mulLeft (n : H ⧸ S) q = ((n * q.out : H) : H ⧸ S) := by
    simp
  rw [this, ec_out T v S hS, map_mul, Module.End.mul_apply]

variable {G : Type} [Group G]

private def ecTw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) : Representation k K V where
  toFun x := (((χ x)⁻¹ : kˣ) : k) • ρ x
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

private theorem ecTw_apply (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ecTw ρ K χ x v = (((χ x)⁻¹ : kˣ) : k) • ρ x v := rfl

private theorem ecTw_smul (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    ρ x v = (χ x : k) • ecTw ρ K χ x v := by
  rw [ecTw_apply, smul_smul]
  simp

private theorem ec_mem_eig (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (v : V) :
    v ∈ eig ρ K χ ↔ ∀ x, ecTw ρ K χ x v = v := by
  refine forall_congr' fun x => ?_
  rw [ecTw_smul ρ K χ]
  exact smul_right_inj (χ x).ne_zero

private theorem ec_mem_tw (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ) (x : K) (v : V) :
    v - ecTw ρ K χ x v ∈ twKer ρ K χ := by
  have h : ρ x v - (χ x : k) • v ∈ twKer ρ K χ := Submodule.subset_span ⟨x, v, rfl⟩
  have h2 := (twKer ρ K χ).smul_mem (-(((χ x)⁻¹ : kˣ) : k)) h
  convert h2 using 1
  rw [ecTw_apply, smul_sub, smul_smul]
  simp
  abel

private theorem ec_fin [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G)
    (χ : K →* kˣ) (hρ : IsSmooth ρ) (hK : IsCompact (K : Set G)) (hχ : IsOpen {x : K | χ x = 1}) (v : V) :
    (ecStab (ecTw ρ K χ) v).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen (ecStab (ecTw ρ K χ) v : Set K) := by
    have h1 : IsOpen ((fun x : K => (x : G)) ⁻¹' {g : G | ρ g v = v}) := (hρ v).preimage continuous_subtype_val
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((h1.inter hχ).mem_nhds (by simp)) ?_)
    rintro x ⟨hx1, hx2⟩
    have a : ρ x v = v := hx1
    have b : χ x = 1 := hx2
    show ecTw ρ K χ x v = v
    rw [ecTw_apply, a, b]
    simp
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

end SlopeTestRemainingChoices

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigCompl :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ), IsSmooth ρ → IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → IsCompl (eig ρ K χ) (twKer ρ K χ) ∧ ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W, ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
  intro k G V _ _ _ _ _ _ _ ρ K χ hρ hK hχ
  have hfin := ec_fin ρ K χ hρ hK hχ
  have part2 : ∀ W : Submodule k V, (∀ x ∈ K, ∀ v ∈ W, ρ x v ∈ W) → ∀ v ∈ W,
      ∃ w ∈ W, w ∈ eig ρ K χ ∧ v - w ∈ twKer ρ K χ := by
    intro W hW v hv
    haveI := hfin v
    set S := (ecStab (ecTw ρ K χ) v).normalCore with hSdef
    have hS : S ≤ ecStab (ecTw ρ K χ) v := Subgroup.normalCore_le _
    letI : Fintype (K ⧸ S) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ S) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨(Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v, ?_, ?_, ?_⟩
    · exact W.smul_mem _ (W.sum_mem fun q _ => W.smul_mem _ (hW _ q.out.2 v hv))
    · exact Submodule.smul_mem _ _ ((ec_mem_eig ρ K χ _).2 fun x => ec_left _ v S hS x)
    · have : v - (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, ecTw ρ K χ q.out v =
          (Fintype.card (K ⧸ S) : k)⁻¹ • ∑ q : K ⧸ S, (v - ecTw ρ K χ q.out v) := by
        rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
          inv_smul_smul₀ hc]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ec_mem_tw ρ K χ _ v)
  have key : ∀ w ∈ twKer ρ K χ, ∃ S₀ : Subgroup K, S₀.FiniteIndex ∧
      ∀ (S : Subgroup K) [S.Normal] [Fintype (K ⧸ S)], S ≤ S₀ → ∑ q : K ⧸ S, ecTw ρ K χ q.out w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨n, u, rfl⟩ := hw
      refine ⟨_, hfin u, fun S _ _ hS => ?_⟩
      rw [ecTw_smul ρ K χ]
      simp only [map_sub, map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [ec_right _ u S hS, sub_self]
    | zero => exact ⟨⊤, inferInstance, fun S _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, ha⟩ := ha
      obtain ⟨B, hB, hb⟩ := hb
      refine ⟨A ⊓ B, inferInstance, fun S _ _ hS => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [ha S (hS.trans inf_le_left), hb S (hS.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA, ha⟩ := ha
      refine ⟨A, hA, fun S _ _ hS => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      rw [ha S hS, smul_zero]
  refine ⟨⟨?_, ?_⟩, part2⟩
  · rw [Submodule.disjoint_def]
    intro w he hw
    obtain ⟨A, hA, h⟩ := key w hw
    letI : Fintype (K ⧸ A.normalCore) := Fintype.ofFinite _
    have hc : (Fintype.card (K ⧸ A.normalCore) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h2 := h A.normalCore A.normalCore_le
    simp only [(ec_mem_eig ρ K χ w).1 he, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k] at h2
    exact (smul_eq_zero.1 h2).resolve_left hc
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨w, -, h1, h2⟩ := part2 ⊤ (fun _ _ _ _ => trivial) v trivial
    have := Submodule.add_mem_sup h1 h2
    simpa using this
end

