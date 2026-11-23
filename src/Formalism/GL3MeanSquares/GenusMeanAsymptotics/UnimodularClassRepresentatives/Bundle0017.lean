module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0009
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]

section Gen

variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem mem_closure_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (s : 𝓞 K) :
    s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} ↔
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨t, ht, rfl⟩ := iha
      obtain ⟨u, hu, rfl⟩ := ihb
      exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, map_mul _ _ _⟩
  · intro hs
    exact Submonoid.subset_closure hs

theorem mem_locF_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, rfl⟩ := (mem_closure_iff hp s).mp hs
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨_, (mem_closure_iff hp _).mpr ⟨t, ht, rfl⟩, hx⟩

theorem le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

theorem locF_mono (𝔭 : Ideal (𝓞 F)) {L M : Submodule (𝓞 K) W} (h : L ≤ M) :
    locF 𝔭 L ≤ locF 𝔭 M :=
  Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h

theorem locF_idem (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) :
    locF 𝔭 (locF 𝔭 L) = locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_locS_idem _ L

theorem iInf_locF (L : Submodule (𝓞 K) W) :
    (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 L) = L := by
  apply le_antisymm
  · intro x hx
    by_contra hxL
    let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 K))
      (Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) W x) L)
    have hmem : ∀ r : 𝓞 F, r ∈ I ↔ algebraMap (𝓞 F) (𝓞 K) r • x ∈ L := by
      intro r
      simp [I]
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 F) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have h2 := (Submodule.mem_iInf _).mp hx ⟨p, hp⟩
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff hp.isPrime L x).mp h2
    exact ht (hIp ((hmem t).mpr htx))
  · exact le_iInf fun 𝔭 => le_locF 𝔭.1 L

end Gen

theorem exists_prime_to_part {c : 𝓞 F} (hc : c ≠ 0) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsMaximal) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮 ≠ 𝔭 → ∃ u : 𝓞 F, u ∉ 𝔮 ∧ c ∣ u * t := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact hp.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨t, htp, fun 𝔮 hq hne => ?_⟩
  have h1 : ¬ 𝔭 ^ multiplicity 𝔭 (Ideal.span {c}) ≤ 𝔮 := by
    intro hle
    exact hne (hp.eq_of_le hq.ne_top (hq.isPrime.le_of_pow_le hle)).symm
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp h1
  refine ⟨u, hu2, ?_⟩
  rw [← Ideal.mem_span_singleton, hb]
  exact Ideal.mul_mem_mul hu1 htb

section Lat

variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_zsmul_le {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsFullLattice K B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  obtain ⟨S, hS⟩ := hA.fg
  choose n hn hnx using fun x : V => Formalism.HermitianLatticesTheory.traceReal_mult B hB x
  refine ⟨∏ x ∈ S, n x, Finset.prod_ne_zero_iff.mpr fun x _ => hn x, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hy
    rw [hm, mul_comm, mul_smul]
    exact zsmul_mem (hnx y) m
  | zero => rw [smul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact B.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact B.smul_mem a hy

theorem algebraMap_intCast_smul (n : ℤ) (x : V) :
    algebraMap (𝓞 F) (𝓞 K) (n : 𝓞 F) • x = n • x := by
  rw [map_intCast, Int.cast_smul_eq_zsmul]

theorem patch {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsFullLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hB : ∀ 𝔭, Submodule.IsFullLattice K (B 𝔭)) (hBs : ∀ 𝔭 ∉ s, B 𝔭 = L₀) :
    Submodule.IsLattice K (⨅ 𝔭, locF 𝔭.1 (B 𝔭)) ∧
      ∀ 𝔭, locF 𝔭.1 (⨅ 𝔮, locF 𝔮.1 (B 𝔮)) = locF 𝔭.1 (B 𝔭) := by
  classical
  choose n₁ hn₁ hn₁x using fun 𝔭 => exists_zsmul_le (hB 𝔭).toIsLattice hL₀
  choose n₂ hn₂ hn₂x using fun 𝔭 => exists_zsmul_le hL₀.toIsLattice (hB 𝔭)
  obtain ⟨N, hN, hN1, hN2⟩ : ∃ N : ℤ, N ≠ 0 ∧ (∀ 𝔭, ∀ x ∈ B 𝔭, N • x ∈ L₀) ∧
      ∀ 𝔭, ∀ x ∈ L₀, N • x ∈ B 𝔭 := by
    refine ⟨∏ 𝔭 ∈ s, (n₁ 𝔭 * n₂ 𝔭),
      Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => mul_ne_zero (hn₁ 𝔭) (hn₂ 𝔭), ?_, ?_⟩
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₂ 𝔭 * m) * n₁ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₁x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭] at hx
        exact zsmul_mem hx _
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₁ 𝔭 * m) * n₂ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₂x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭]
        exact zsmul_mem hx _
  set Λ : Submodule (𝓞 K) V := ⨅ 𝔭, locF 𝔭.1 (B 𝔭) with hΛ
  have hΛle : ∀ 𝔭, Λ ≤ locF 𝔭.1 (B 𝔭) := fun 𝔭 => iInf_le _ 𝔭
  have h2 : ∀ x ∈ L₀, N • x ∈ Λ := by
    intro x hx
    rw [hΛ, Submodule.mem_iInf]
    exact fun 𝔭 => le_locF 𝔭.1 _ (hN2 𝔭 x hx)
  have h3 : ∀ x ∈ Λ, N • x ∈ L₀ := by
    intro x hx
    rw [← iInf_locF (F := F) L₀, Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp (hΛle 𝔭 hx)
    refine (mem_locF_iff 𝔭.2.isPrime _ _).mpr ⟨t, ht, ?_⟩
    rw [smul_comm]
    exact hN1 𝔭 _ htx
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let φ : V →ₗ[𝓞 K] V := N • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have : N • x = N • y := hxy
      rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K] at this
      exact smul_right_injective V hNK this
    apply Submodule.fg_of_fg_map_injective φ hφ
    have hle : Λ.map φ ≤ L₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact h3 x hx
    exact hL₀.fg.of_le hle
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro 𝔭
    apply le_antisymm
    · calc locF 𝔭.1 Λ ≤ locF 𝔭.1 (locF 𝔭.1 (B 𝔭)) := locF_mono _ (hΛle 𝔭)
        _ = _ := locF_idem _ _
    · intro x hx
      obtain ⟨t₀, ht₀, hy⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp hx
      have hc : ((N * N : ℤ) : 𝓞 F) ≠ 0 := by
        exact_mod_cast mul_ne_zero hN hN
      obtain ⟨t, ht, hq⟩ := exists_prime_to_part hc 𝔭.2
      refine (mem_locF_iff 𝔭.2.isPrime _ x).mpr
        ⟨t * t₀, fun h => (𝔭.2.isPrime.mem_or_mem h).elim ht ht₀, ?_⟩
      rw [map_mul, mul_smul]
      generalize algebraMap (𝓞 F) (𝓞 K) t₀ • x = y at hy
      have hcy : (N * N) • y ∈ Λ := by
        rw [mul_smul]
        exact h2 _ (hN1 𝔭 y hy)
      rw [hΛ, Submodule.mem_iInf]
      intro 𝔮
      by_cases hqp : 𝔮 = 𝔭
      · rw [hqp]
        exact Submodule.smul_mem _ _ (le_locF _ _ hy)
      · obtain ⟨u, hu, d, hd⟩ := hq 𝔮.1 𝔮.2 (fun h => hqp (Subtype.ext h))
        rw [← locF_idem]
        refine (mem_locF_iff 𝔮.2.isPrime _ _).mpr ⟨u, hu, ?_⟩
        rw [← mul_smul, ← map_mul, hd, mul_comm, map_mul, mul_smul, algebraMap_intCast_smul]
        exact Submodule.smul_mem _ _ (hΛle 𝔮 hcy)

end Lat

end Formalism.HermitianLattices.Ext.L3.LocF
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsFixF
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def starFixed (K : Type) [Field K] [CharZero K] [StarRing K] : IntermediateField ℚ K where
  carrier := {a : K | star a = a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  algebraMap_mem' := by
    intro q
    exact map_ratCast (starRingEnd K) q
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [star_inv₀, ha]

theorem exists_fixF (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F K), IsFixF K F := by
  haveI : FiniteDimensional ℚ (starFixed K) := IntermediateField.finiteDimensional_left (starFixed K)
  haveI : NumberField (starFixed K) := ⟨⟩
  refine ⟨starFixed K, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.2

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def perpSpace (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) : Submodule K V := LinearMap.ker (h x₀)

def perpForm (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) :
    ↥(perpSpace h x₀) →ₗ⋆[K] ↥(perpSpace h x₀) →ₗ[K] K :=
  (h.comp (perpSpace h x₀).subtype).compl₂ (perpSpace h x₀).subtype

def vecSplitPerp (h : V →ₗ⋆[K] V →ₗ[K] K) {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    VecSplit h (perpForm h x₀) where
  x₀ := x₀
  ι := (perpSpace h x₀).subtype
  inj := Subtype.val_injective
  hx₀ := hx
  isom := fun _ _ => rfl
  orth := fun a => LinearMap.mem_ker.mp a.2
  cover := fun v => by
    refine ⟨h x₀ v / h x₀ x₀, ⟨v - (h x₀ v / h x₀ x₀) • x₀, ?_⟩, ?_⟩
    · change v - (h x₀ v / h x₀ x₀) • x₀ ∈ LinearMap.ker (h x₀)
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
    · simp

private theorem star_sesq_eq_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (a b : V) :
    star (h a b) = h b a := by
  first | exact hs a b | exact hs.eq a b

theorem VecSplit.finrank_add_one {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') : finrank K V' + 1 = finrank K V := by
  let f : K × V' →ₗ[K] V := LinearMap.coprod (LinearMap.toSpanSingleton K V S.x₀) S.ι
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, a⟩ hca
      have h1 : c • S.x₀ + S.ι a = 0 := by simpa [f] using hca
      have h2 : h S.x₀ (c • S.x₀ + S.ι a) = 0 := by rw [h1, map_zero]
      rw [map_add (f := _), map_smul, S.orth, add_zero, smul_eq_mul] at h2
      have hc : c = 0 := (mul_eq_zero.mp h2).resolve_right S.hx₀
      subst hc
      have h3 : S.ι a = 0 := by simpa using h1
      have ha : a = 0 := S.inj (by rw [h3, map_zero])
      simp [ha]
    · intro v
      obtain ⟨c, a, hv⟩ := S.cover v
      exact ⟨(c, a), by simp [f, hv]⟩
  have := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

theorem finrank_perpSpace {h : V →ₗ⋆[K] V →ₗ[K] K} {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    finrank K (perpSpace h x₀) + 1 = finrank K V :=
  VecSplit.finrank_add_one (vecSplitPerp h hx)

theorem VecSplit.isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hd : IsTotPosDef h) : IsTotPosDef h' := by
  intro a ha φ
  rw [← S.isom]
  exact hd _ (fun h0 => ha (S.inj (by rw [h0, map_zero]))) φ

theorem VecSplit.isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hs : h.IsSymm) : h'.IsSymm := by
  have H : ∀ a b : V', star (h' a b) = h' b a := by
    intro a b
    rw [← S.isom, ← S.isom]
    exact star_sesq_eq_swap_of_isSymm hs _ _
  first | exact H | exact ⟨H⟩

theorem exists_vec_of_hermRep (hH : HermRepUnram) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) (hV : 2 ≤ finrank K V)
    (n : K) (hn : star n = n) (hpos : TotPos n) : ∃ x : V, h x x = n := by
  have hne : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hx φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hfr := finrank_perpSpace (h := h) (hne x hx)
  obtain ⟨y', hy'⟩ : ∃ y : ↥(perpSpace h x), y ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hy0 : y'.1 ≠ 0 := fun h0 => hy' (Subtype.ext h0)
  have hxy : h x y'.1 = 0 := LinearMap.mem_ker.mp y'.2
  have hyx : h y'.1 x = 0 := by rw [← star_sesq_eq_swap_of_isSymm hs, hxy, star_zero]
  obtain ⟨s, t, hst⟩ := hH K hK (h x x) (h y'.1 y'.1) n (star_sesq_eq_swap_of_isSymm hs x x) (star_sesq_eq_swap_of_isSymm hs _ _) hn
    (fun φ => hd x hx φ) (fun φ => hd _ hy0 φ) hpos
  refine ⟨star s • x + star t • y'.1, ?_⟩
  simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    hxy, hyx, starRingEnd_apply, star_star]
  linear_combination hst

theorem VecSplit.le_dual_of_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hs : h.IsSymm) (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ) (hx : S.x₀ ∈ Λ) :
    S.adjoin (S.cut Λ) ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin (S.cut Λ)) := by
  have hle : S.adjoin (S.cut Λ) ≤ Λ :=
    sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (Submodule.map_comap_le _ _)
  refine ⟨hle, fun x hx' => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro y hy
  exact hΛ y (hle hy) x hx'

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassRatioEqLvalue
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem massRatio_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  have hv := vInv_pos K
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  refine mul_pos (div_pos (pow_pos (mul_pos ?_ (pow_pos (div_pos hv Real.pi_pos) _)) _) ?_)
    (lValEta_pos hK M hM)
  · exact_mod_cast Nat.factorial_pos _
  · exact Real.sqrt_pos.mpr (pow_pos (mul_pos two_pos hv) _)

theorem massRatio_eq_lvalue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 2 ≤ m) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K m =
      (((m - 1).factorial : ℝ) / Real.pi ^ m) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * m) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F m := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [lValEta_eq_lValEtaF hK hF m hm, mul_comm (Formalism.HermitianLatticesTheory.fDeg K) m, pow_mul, ← mul_pow, div_pow]
  congr 3
  ring

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section Defs

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def eA (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {e : ℕ | ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A}

def repRatio (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℝ :=
  (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * alphaN h L 𝔭 n / alphaL h L 𝔭

end Defs

def LIRatio : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (L L₀ : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      Submodule.IsFullLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
      Submodule.IsFullLattice K L₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ →
      psiP S L 𝔭 * repRatio h L₀ 𝔭 n = psiP S L₀ 𝔭 * repRatio h L 𝔭 n

def LIPin : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsFullLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
        repRatio h L₀ 𝔭 n ≠ 0 ∧
        psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
          alphaStd K 𝔭 (finrank K V - 1) * repRatio h L₀ 𝔭 n

end Formalism.HermitianLattices.Ext.L3
end
end

