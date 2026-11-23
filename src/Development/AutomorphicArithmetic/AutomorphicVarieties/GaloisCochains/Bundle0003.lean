module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.StrGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0006
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.B1p
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC
open scoped Pointwise

private theorem exists_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A₀ A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h₀ : IsPlaceOver A₀ v) (hA : IsPlaceOver A v) :
    ∃ u : G F Ω, ∀ x ∈ Ine (F := F) A, u⁻¹ * x * u ∈ Dec (F := F) A₀ := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) h₀ hA
  have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ A ↔ x ∈ A₀ := fun x => by
    show g • x ∈ A ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  exact ⟨g, fun x hx => conjGal_mem_Dec h hm hx.1⟩

theorem UpperTheory.V.GC.b1p :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc (chRep (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)) fun _ => ⊥) ≤ C₀ := by
  intro F Ω _ _ _ _ _ l hl k _ _ Φ S K π ι A pl e c L h3 C₀ hC
  haveI := L.g.normal
  have hω : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
    (isOpen_discrete {(1 : (ZMod (l ^ 1))ˣ)}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod
  have hidx : ¬ l ∣ (K ⊓ (cycMod F Ω l 1).ker).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 : (K ⊓ (cycMod F Ω l 1).ker).index ∣ K.index * (cycMod F Ω l 1).ker.index := by
      rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ (cycMod F Ω l 1).ker ≤ K), mul_comm,
        Subgroup.inf_relIndex_left]
      exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_index_of_normal _ _)
    rcases (hl.out.dvd_mul).1 (h.trans h1) with h2 | h2
    · exact L.g.idx h2
    · rw [Subgroup.index_ker] at h2
      have h4 := h2.trans (Subgroup.card_subgroup_dvd_card _)
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h4
      have h5 := hl.out.two_le
      have := Nat.le_of_dvd (by omega) h4
      omega
  have key := strGen F Ω l k ⊤ (K ⊓ (cycMod F Ω l 1).ker) le_top (L.g.isOpen.inter hω) hidx Φ.Γ
    (π.comp (Subgroup.subtype ⊤)) (L.g.cont.comp continuous_subtype_val)
    (fun y => by
      obtain ⟨x, hx⟩ := L.g.onto y
      exact ⟨⟨x, trivial⟩, hx⟩)
    Φ.V Φ.Gv Φ.loc (Φ.Ψ⁻¹ ^ 2 * Φ.delK k)
    (fun u hu => by
      have h1 := L.K_del _ hu.1
      have h2 := L.K_Ψ _ hu.1
      simp [Frame.delK, h1, h2])
    (fun B u hu hK => by
      obtain ⟨p1, p2, -⟩ := Kum.placeDict F Ω
      by_cases hB : B = ⊤
      · left
        rw [hB, p1, Subgroup.mem_bot] at hu
        simp [hu]
      obtain ⟨w, hw⟩ := p2 B hB
      by_cases hS : w ∈ S
      · right
        obtain ⟨v, rfl⟩ := (L.loc.mem w).2 (L.only w hS)
        obtain ⟨g, hg⟩ := exists_conj (L.loc.isOver v) hw
        have h1 := hg _ hu
        rw [← L.loc.range v] at h1
        obtain ⟨s, hs⟩ := h1
        refine ⟨v, s, π g, ?_⟩
        rw [L.loc_eq, hs]
        simp [mul_assoc]
      · left
        have : u.1 ∈ π.ker := by
          rw [L.g.ker]
          refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
          simp only [Set.mem_iUnion]
          exact ⟨w, hS, B, hw, hu, hK.1⟩
        exact this)
  haveI : IsEmpty {v // ∀ s, (Φ.Ψ⁻¹ ^ 2 * Φ.delK k) (Φ.loc v s) = 1} := ⟨fun ⟨v, hv⟩ => by
    obtain ⟨g, hg⟩ := h3 v
    have h1 : Φ.del (Φ.loc v g) = 1 := (Φ.loc0 v g).2
    have h2 := hv g
    apply hg
    simpa [Frame.delK, h1] using h2⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, add_zero, Cardinal.lift_id] at key
  exact key.trans hC
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Imports
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

theorem UpperTheory.V.GC.phi :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → Alg.PhiCond Φ.Γ l := by
  intro F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c h
  exact UpperTheory.V.GC.phiGam F Ω l S K Φ.Γ π h.g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.PsiLocalPairEqLocal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

open scoped Pointwise in
private theorem ine_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (v : G F Ω)
    (B : ValuationSubring Ω) (g : G F Ω) (hg : g ∈ Ine (F := F) (v • B)) : v⁻¹ * g * v ∈ Ine (F := F) B := by
  have hl : IsLift (RingEquiv.refl F) v.toRingEquiv := fun y => v.commutes y
  have hA : ∀ x : Ω, v.toRingEquiv x ∈ v • B ↔ x ∈ B := fun x => by
    show v • x ∈ v • B ↔ x ∈ B
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have e : v⁻¹ * g * v = conjGal hl g := AlgEquiv.ext fun _ => rfl
  rw [e]
  exact conjGal_mem_Ine hl hA hg

private theorem not_dvd_ker_index {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (χ : H →* (ZMod (l ^ 1))ˣ) :
    ¬ l ∣ χ.ker.index := by
  intro h
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [Subgroup.index_ker] at h
  have h2 := h.trans (Subgroup.card_subgroup_dvd_card χ.range)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h2
  have h3 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h2
  omega

private theorem Psi_local_pair_eq_local {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (Φ : Fr.Frame l k) (p : Φ.V × Bool)
    (s : Φ.Gv p.1) : Φ.Ψ (Φ.loc2 p s).1 = Φ.Ψ (Φ.loc p.1 s) := by
  obtain ⟨v, b⟩ := p
  cases b
  · rfl
  · show Φ.Ψ (Φ.c * Φ.loc v s * Φ.c⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem UpperTheory.V.GC.b1 :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ → Module.rank k (H1C (k := k) (W := k) Φ.loc2 (chRep (Φ.Ψ⁻¹.comp Φ.del.ker.subtype)) fun _ => ⊥) ≤ C₀ := by
  intro F Ω _ _ _ _ _ l hl k _ _ Φ S K π ι A pl e c h hΨ C₀ hC
  haveI := h.g.normal
  let U : Subgroup (G F Ω) := Φ.del.ker.comap π
  let π' : U →* Φ.del.ker := π.subgroupComap Φ.del.ker
  have hπ' : ∀ u : U, (π' u).1 = π u.1 := fun _ => rfl
  have hKU : K ≤ U := fun g hg => h.K_del g hg
  have hω : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
    by
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
      have e1 : ((cycMod F Ω l 1).ker : Set (G F Ω)) =
          (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
        ext g
        rw [Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
          RingHom.mem_ker, map_sub, map_one, sub_eq_zero, SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
        rfl
      rw [e1]
      refine (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))).preimage ?_
      exact (Units.continuous_val.comp (continuous_cycZ F Ω l)).sub continuous_const
  have hidx : ¬ l ∣ (K ⊓ (cycMod F Ω l 1).ker).relIndex U := by
    intro hd
    have h1 := hd.trans (Subgroup.relIndex_dvd_index_of_le (inf_le_left.trans hKU : K ⊓ (cycMod F Ω l 1).ker ≤ U))
    rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ (cycMod F Ω l 1).ker ≤ K), Subgroup.inf_relIndex_left] at h1
    rcases (Nat.Prime.dvd_mul hl.out).1 h1 with h2 | h2
    · exact not_dvd_ker_index l _ (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
    · exact h.g.idx h2
  have hplaces (A : ValuationSubring Ω) : (A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v) ∧ (A = ⊤ → Ine (F := F) A = ⊥) := by
    have hint : ∀ z : Ω, IsIntegral ℤ z → A.valuation z ≤ 1 := by
      intro z hz
      obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp (hz.tower_top (A := A))
      exact A.valuation_le_one y
    have hOk : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) ≤ 1 := fun x =>
      hint _ x.isIntegral_coe.algebraMap
    have htop : A = ⊤ → ∀ y : Ω, A.valuation y < 1 → y = 0 := by
      intro hA y hy
      by_contra h0
      have h2 : A.valuation y⁻¹ ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _)
      have h3 : A.valuation y * A.valuation y⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]
      have h4 : A.valuation y * A.valuation y⁻¹ < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' h2) hy
      exact absurd h3 (ne_of_lt h4)
    refine ⟨?_, ?_⟩
    · intro hA
      let p : Ideal (𝓞 F) :=
        { carrier := {x | A.valuation (algebraMap F Ω (x : F)) < 1}
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq, map_add (f := _)] at *
            exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
          zero_mem' := by simp
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
            exact lt_of_le_of_lt (mul_le_of_le_one_left' (hOk c)) hx }
      have hprime : p.IsPrime := by
        refine ⟨?_, ?_⟩
        · rw [Ne, Ideal.eq_top_iff_one]
          show ¬ A.valuation (algebraMap F Ω ((1 : 𝓞 F) : F)) < 1
          simp
        · intro x y hxy
          change A.valuation (algebraMap F Ω ((x * y : 𝓞 F) : F)) < 1 at hxy
          change A.valuation (algebraMap F Ω (x : F)) < 1 ∨ A.valuation (algebraMap F Ω (y : F)) < 1
          simp only [map_mul] at hxy
          by_contra h
          push_neg at h
          have hx1 : A.valuation (algebraMap F Ω (x : F)) = 1 := le_antisymm (hOk x) h.1
          have hy1 : A.valuation (algebraMap F Ω (y : F)) = 1 := le_antisymm (hOk y) h.2
          rw [hx1, hy1, one_mul] at hxy
          exact lt_irrefl _ hxy
      have hne : p ≠ ⊥ := by
        intro hbot
        apply hA
        have hk : ∀ y : F, A.valuation (algebraMap F Ω y) ≤ 1 := by
          intro y
          obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
          have hb0 : (b : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero hb
          have hbv : A.valuation (algebraMap F Ω (algebraMap (𝓞 F) F b)) = 1 := by
            refine le_antisymm (hOk b) (not_lt.mp fun h => hb0 ?_)
            have hbp : b ∈ p := h
            rw [hbot] at hbp
            exact (Submodule.mem_bot _).mp hbp
          rw [map_div₀, map_div₀, hbv, div_one]
          exact hOk a
        have hf : ∀ y : F, algebraMap F Ω y ∈ A := fun y => (A.valuation_le_one_iff _).mp (hk y)
        let f : F →+* A := (algebraMap F Ω).codRestrict A hf
        have hcomp : (algebraMap A Ω).comp f = algebraMap F Ω := by
          ext y
          rfl
        rw [eq_top_iff]
        intro z _
        have hz : IsIntegral A z := by
          obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := F) z
          refine ⟨q.map f, hqm.map f, ?_⟩
          rw [Polynomial.eval₂_map, hcomp]
          exact hq
        obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hz
        exact y.2
      exact ⟨⟨p, hprime, hne⟩, fun x => Iff.rfl⟩
    · intro hA
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      obtain ⟨-, hσ⟩ := hσ
      ext z
      have h1 := hσ z ((A.valuation_le_one_iff _).mpr (by rw [hA]; exact ValuationSubring.mem_top _))
      have h2 := htop hA _ h1
      rw [sub_eq_zero] at h2
      simpa using h2
  have key := strGen F Ω l k U (K ⊓ (cycMod F Ω l 1).ker) (inf_le_left.trans hKU) (h.g.isOpen.inter hω) hidx
    Φ.del.ker π' ((h.g.cont.comp continuous_subtype_val).subtype_mk _)
    (π.subgroupComap_surjective_of_surjective _ h.g.onto) (Φ.V × Bool) (fun p => Φ.Gv p.1) Φ.loc2
    (Φ.Ψ⁻¹.comp Φ.del.ker.subtype) (fun u hu => by
      show (Φ.Ψ (π u.1))⁻¹ = 1
      rw [h.K_Ψ _ hu.1, inv_one]) (fun B u hu huK => by
      by_cases hB : B = ⊤
      · left
        rw [((hplaces B).2 hB), Subgroup.mem_bot] at hu
        exact Subtype.ext (by rw [hπ', hu, map_one]; rfl)
      obtain ⟨w, hw⟩ := (hplaces B).1 hB
      by_cases hS : w ∈ S
      · right
        obtain ⟨v, rfl⟩ := (h.loc.mem w).2 (h.only w hS)
        obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (h.loc.isOver v) hw
        have h1 := Ine_le_Dec _ (ine_conj g _ _ hu)
        rw [← h.loc.range v] at h1
        obtain ⟨s, hs⟩ := h1
        have h2 : π u.1 = π g * Φ.loc v s * (π g)⁻¹ := by
          rw [h.loc_eq, hs, ← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
        rcases Int.units_eq_one_or (Φ.del (π g)) with h3 | h3
        · exact ⟨(v, false), s, ⟨π g, h3⟩, Subtype.ext h2⟩
        · refine ⟨(v, true), s, ⟨π g * Φ.c⁻¹, ?_⟩, Subtype.ext (h2.trans ?_)⟩
          · rw [MonoidHom.mem_ker, map_mul, map_inv, h3, h.del_c, mul_inv_cancel]
          · show _ = π g * Φ.c⁻¹ * (Φ.c * Φ.loc v s * Φ.c⁻¹) * (π g * Φ.c⁻¹)⁻¹
            group
      · left
        refine Subtype.ext ?_
        show π u.1 = 1
        rw [← MonoidHom.mem_ker, h.g.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨w, hS, B, hw, hu, huK.1⟩)
  haveI : IsEmpty {p : Φ.V × Bool // ∀ s, (Φ.Ψ⁻¹.comp Φ.del.ker.subtype) (Φ.loc2 p s) = 1} := ⟨fun p => by
    obtain ⟨s, hs⟩ := hΨ p.1.1
    have h1 : (Φ.Ψ (Φ.loc2 p.1 s).1)⁻¹ = 1 := p.2 s
    rw [Psi_local_pair_eq_local, inv_eq_one] at h1
    exact hs (by rw [h1, one_pow])⟩
  rw [Nat.card_of_isEmpty, Nat.cast_zero, add_zero, Cardinal.lift_id] at key
  exact key.trans hC
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.TameEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem tameEq_cochain {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (J : Subgroup Γ) [hJn : J.Normal]
    (hJ : ∀ j ∈ J, ρ j = 1) (f : J → M) (hf : IsLocallyConstant f) (hadd : ∀ a b, f (a * b) = f a + f b) :
    ∃ c : Γ → M, IsLocallyConstant c ∧ ∀ g (j : J), c (g * j) = c g + ρ g (f j) := by
  classical
  have f1 : f 1 = 0 := by
    have e := hadd 1 1
    rw [mul_one] at e
    exact left_eq_add.1 e
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.1 (hf {0})
  have hKo : IsOpen (⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m}) :=
    isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (hρ.comp (continuous_id.prodMk continuous_const))
  have hW1 : (1 : Γ) ∈ W := by
    have : (1 : J) ∈ Subtype.val ⁻¹' W := by rw [hW]; exact f1
    exact this
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hWo.inter hKo)
    ⟨hW1, by simp⟩
  have hUρ : ∀ u ∈ U, ρ u = 1 := fun u hu => LinearMap.ext fun m => Set.mem_iInter.1 (hU hu).2 m
  have hUf : ∀ j : J, j.1 ∈ U → f j = 0 := fun j hj => by
    have : j ∈ Subtype.val ⁻¹' W := (hU hj).1
    rw [hW] at this
    exact this
  have hUn : U.toSubgroup.Normal := inferInstance
  let f' : Γ → M := fun g => if h : ∃ j : J, j.1⁻¹ * g ∈ U then f h.choose else 0
  have hf' : ∀ (g : Γ) (j : J), j.1⁻¹ * g ∈ U → f' g = f j := fun g j hj => by
    have h : ∃ j : J, j.1⁻¹ * g ∈ U := ⟨j, hj⟩
    have e : f' g = f h.choose := dif_pos h
    have h2 : (j⁻¹ * h.choose).1 ∈ U := by
      have := mul_mem hj (inv_mem h.choose_spec)
      simpa [mul_assoc] using this
    have e2 := hadd j (j⁻¹ * h.choose)
    rw [mul_inv_cancel_left, hUf _ h2, add_zero] at e2
    rw [e, e2]
  let N : Subgroup Γ := J ⊔ U.toSubgroup
  let r : Γ → Γ := fun g => (g : Γ ⧸ N).out
  have hr : ∀ g, ∃ j : J, j.1⁻¹ * ((r g)⁻¹ * g) ∈ U := fun g => by
    have h1 : (r g)⁻¹ * g ∈ ((J ⊔ U.toSubgroup : Subgroup Γ) : Set Γ) :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : Γ ⧸ N))
    rw [Subgroup.normal_mul] at h1
    obtain ⟨j, hj, u, hu, e⟩ := h1
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [← e]
    show j⁻¹ * (j * u) ∈ U
    rw [inv_mul_cancel_left]
    exact hu
  have hrN : ∀ g, ∀ n ∈ N, r (g * n) = r g := fun g n hn => by
    simp only [r, QuotientGroup.mk_mul_of_mem g hn]
  refine ⟨fun g => ρ (r g) (f' ((r g)⁻¹ * g)), ?_, fun g j => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' U, U.isOpen.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have hx' : g⁻¹ * x ∈ U := hx
    have e : r x = r g := by
      have := hrN g _ (Subgroup.mem_sup_right (S := J) (T := U.toSubgroup) hx')
      rwa [mul_inv_cancel_left] at this
    obtain ⟨j, hj⟩ := hr g
    rw [e, hf' _ j hj, hf' _ j (by simpa [mul_assoc] using mul_mem hj hx')]
  · obtain ⟨i, hi⟩ := hr g
    have e : ρ g = ρ (r g) := by
      have h1 : g = r g * (i.1 * (i.1⁻¹ * ((r g)⁻¹ * g))) := by group
      conv_lhs => rw [h1]
      rw [map_mul, map_mul, hJ _ i.2, hUρ _ hi, mul_one, mul_one]
    have h2 : (i * j).1⁻¹ * ((r g)⁻¹ * (g * j)) ∈ U := by
      have h3 : j.1⁻¹ * (i.1⁻¹ * ((r g)⁻¹ * g)) * j.1⁻¹⁻¹ ∈ U := hUn.conj_mem _ hi j.1⁻¹
      simpa [mul_assoc] using h3
    show ρ (r (g * j)) (f' ((r (g * j))⁻¹ * (g * j))) = ρ (r g) (f' ((r g)⁻¹ * g)) + _
    rw [hrN g j (Subgroup.mem_sup_left j.2), hf' _ _ h2, hf' _ _ hi, hadd, map_add (f := _), e]

private theorem tameEq_ext {k Γ M : Type} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation k Γ M) (hρ : ContAction ρ) (J : Subgroup Γ) [hJn : J.Normal]
    (hJ : ∀ j ∈ J, ρ j = 1)
    (h2 : ∀ z : Z2 ρ, (∀ s t, ∀ j ∈ J, ∀ j' ∈ J, z.1 (s * j, t * j') = z.1 (s, t)) → ∃ b : Γ → M, IsLocallyConstant b ∧
      (∀ s, ∀ j ∈ J, b (s * j) = b s) ∧ ∀ s t, z.1 (s, t) = ρ s (b t) - b (s * t) + b s)
    (f : J → M) (hf : IsLocallyConstant f) (hadd : ∀ a b, f (a * b) = f a + f b)
    (heq : ∀ (d : Γ) (j j' : J), j'.1 = d * j.1 * d⁻¹ → f j' = ρ d (f j)) :
    ∃ x : Z1 ρ, ∀ j : J, x.1 j = f j := by
  obtain ⟨c, hc, hcj⟩ := tameEq_cochain ρ hρ J hJ f hf hadd
  obtain ⟨b, hb, hbj, hbz⟩ := h2 ⟨d1 ρ c, coboundaries2_le_cocycles2 ρ hρ ⟨c, hc.continuous, rfl⟩⟩ (fun s t j hj j' hj' => by
    show ρ (s * j) (c (t * j')) - c (s * j * (t * j')) + c (s * j) = ρ s (c t) - c (s * t) + c s
    have hm : t⁻¹ * j * t ∈ J := by simpa using hJn.conj_mem j hj t⁻¹
    have e : s * j * (t * j') = s * t * ((⟨t⁻¹ * j * t, hm⟩ * ⟨j', hj'⟩ : J) : Γ) := by
      simp [mul_assoc]
    have e2 := heq t ⟨t⁻¹ * j * t, hm⟩ ⟨j, hj⟩ (by simp [mul_assoc])
    rw [e, hcj, hcj s ⟨j, hj⟩, hcj t ⟨j', hj'⟩, hadd, e2]
    simp only [map_mul, map_add (f := _), hJ j hj, mul_one, Module.End.mul_apply]
    abel)
  have hz : c - b ∈ Z1 ρ := ⟨hc.continuous.sub hb.continuous, fun s t => by
    have e : ρ s (c t) - c (s * t) + c s = _ := hbz s t
    simp only [Pi.sub_apply, map_sub]
    calc c (s * t) - b (s * t)
        = c s - b s + (ρ s (c t) - ρ s (b t)) -
          ((ρ s (c t) - c (s * t) + c s) - (ρ s (b t) - b (s * t) + b s)) := by abel
      _ = _ := by rw [e, sub_self, sub_zero]⟩
  refine ⟨⟨c - b, hz⟩, fun j => ?_⟩
  have e1 := hz.2 1 1
  have e2 := hcj 1 j
  have e3 := hbj 1 j j.2
  simp only [Pi.sub_apply, one_mul, map_one, Module.End.one_apply] at e1 e2 e3
  show c j - b j = f j
  rw [e2, e3, add_sub_right_comm, left_eq_add.1 e1, zero_add]

open Formalism.GaloisCohomology in
theorem UpperTheory.V.GC.tameEq :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (K : Subgroup (G F Ω)) [K.Normal], IsOpen (K : Set (G F Ω)) → ¬ l ∣ K.index →
    ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (G F Ω) M), ContAction ρ → (∀ g ∈ Ine (F := F) A ⊓ K, ρ g = 1) →
    Module.Finite k (eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K)) ∧ finrank k (eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K)) = finrank k (H2 (ρ.comp (Dec (F := F) A).subtype)) := by
  intro lf lt le F Ω _ _ _ _ _ l _ v A hA hl K _ hKo hKi k _ _ _ M _ _ _ _ _ ρ hρ hJ
  haveI : IsGalois F Ω := {}
  haveI : Finite M := Module.finite_of_finite k
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  let σ : Representation k (Dec (F := F) A) M := ρ.comp (Dec (F := F) A).subtype
  have hσ : ContAction σ := hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let I := (Ine (F := F) A).subgroupOf (Dec (F := F) A)
  let J := (Ine (F := F) A ⊓ K).subgroupOf (Dec (F := F) A)
  haveI hIn : I.Normal := inferInstance
  haveI hJn : J.Normal := ⟨fun n hn g => ⟨hIn.conj_mem n hn.1 g, ‹K.Normal›.conj_mem n.1 hn.2 g.1⟩⟩
  have hJI : J ≤ I := Subgroup.comap_mono inf_le_left
  have hidx : ¬ l ∣ J.relIndex I := by
    rw [Subgroup.relIndex_subgroupOf (Ine_le_Dec _), Subgroup.inf_relIndex_left]
    exact fun h => hKi (h.trans (Subgroup.relIndex_dvd_index_of_normal K _))
  have hJc : IsClosed (J : Set (Dec (F := F) A)) :=
    ((isClosed_Ine A).inter (K.isClosed_of_isOpen hKo)).preimage continuous_subtype_val
  have hJσ : ∀ j ∈ J, σ j = 1 := fun j hj => hJ j.1 hj
  obtain ⟨φ, -, h1, h2⟩ := decZhat F Ω v A hA
  obtain ⟨a1, -, -, a2, -⟩ := locEuler lf lt le F Ω l v A hA k M σ hσ
  have a3 := a2 hl
  have hur : finrank k (H1ur σ J) = finrank k (H0 σ) := by
    rw [X.urIndex l σ hσ I J hJI hidx, X.urAbs σ hσ I φ h1 h2]
  let e : (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) → Dec (F := F) A := fun j => ⟨j.1, Ine_le_Dec A j.2.1⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  let p : Z1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    { toFun := fun z => ⟨fun j => z.1 (e j), (IsLocallyConstant.iff_continuous _).2 (z.2.1.comp he), fun a b => by
          have := z.2.2 (e a) (e b)
          rw [hJσ (e a) a.2] at this
          exact this, fun d hd j j' h => by
          have h3 := z.2.2 (e j') ⟨d, hd⟩
          have h4 := z.2.2 ⟨d, hd⟩ (e j)
          have h5 : e j' * ⟨d, hd⟩ = ⟨d, hd⟩ * e j := Subtype.ext (by simp [e, h])
          rw [hJσ (e j') j'.2, h5, h4, add_comm] at h3
          exact (add_right_cancel h3).symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hp : ∀ z, p z = 0 ↔ ∀ j ∈ J, z.1 j = 0 := fun z =>
    ⟨fun h j hj => congrFun (congrArg Subtype.val h) ⟨j.1, hj⟩, fun h => Subtype.ext (funext fun j => h (e j) j.2)⟩
  let q : H1 σ →ₗ[k] eqHom ρ (Dec (F := F) A) (Ine (F := F) A ⊓ K) :=
    Submodule.liftQ _ p fun z hz => (hp z).2 fun j hj => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
      have : z.1 j = σ j m - m := hm j
      rw [this, hJσ j hj]
      simp
  have hk : LinearMap.ker q = H1ur σ J := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (hp z).trans (Iff.trans ?_ (Submodule.Quotient.mk_eq_zero _).symm)
    refine Iff.trans ?_ (mem_coboundaries1 _ _).symm
    constructor
    · exact fun h => ⟨0, fun j => (h j.1 j.2).trans (by simp)⟩
    · rintro ⟨m, hm⟩ j hj
      have : z.1 j = σ j m - m := hm ⟨j, hj⟩
      rw [this, hJσ j hj]
      simp
  have hq : Function.Surjective q := by
    intro f
    let e' : J → (Ine (F := F) A ⊓ K : Subgroup (G F Ω)) := fun j => ⟨j.1.1, j.2⟩
    have he' : Continuous e' := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    obtain ⟨x, hx⟩ := tameEq_ext σ hσ J hJσ (H2_unramified_inflation l _ k M σ hσ I J φ hJI hJc hidx hJσ h1 h2)
      (fun j => f.1 (e' j)) (f.2.1.comp_continuous he') (fun a b => f.2.2.1 (e' a) (e' b))
      (fun d j j' h => f.2.2.2 d.1 d.2 (e' j) (e' j') (congrArg Subtype.val h))
    exact ⟨Submodule.Quotient.mk x, Subtype.ext (funext fun j => hx ⟨e j, j.2⟩)⟩
  refine ⟨Module.Finite.of_surjective q hq, ?_⟩
  have a4 := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hq, finrank_top, hk, hur, a3] at a4
  show _ = finrank k (H2 σ)
  omega
end

