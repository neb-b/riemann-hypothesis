module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem val_modEq {N : ℕ} [NeZero N] {x : ZMod N} {a : ℕ} (h : x = (a : ZMod N)) : x.val ≡ a [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, h]

private theorem unitsMap_val {g N : ℕ} [NeZero g] [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g).val ≡ (u : ZMod N).val [MOD g] := by
  apply val_modEq
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]

private theorem down (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (K : Subgroup (ZMod g)ˣ) (hK : ∀ u, u ∈ K ↔ P (u : ZMod g).val)
    (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (h : g ∣ N)
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N)
    (hj : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔ P a)) : HasLevel E g K := by
  refine ((levChange E N).2 g h K).2 ⟨j, ζ, hζ, fun τ u hu => ?_⟩
  rw [hj τ _ hu, Subgroup.mem_comap, hK]
  exact (hP _ _ (unitsMap_val h u)).symm

private theorem exists_sub (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (h1 : P 1) (hm : ∀ a b, P a → P b → P (a * b)) :
    ∃ K : Subgroup (ZMod g)ˣ, ∀ u, u ∈ K ↔ P (u : ZMod g).val := by
  let S : Submonoid (ZMod g)ˣ :=
    { carrier := {u | P (u : ZMod g).val}
      one_mem' := (hP _ _ (val_modEq (a := 1) (by simp))).2 h1
      mul_mem' := fun {u v} hu hv =>
        (hP _ _ (val_modEq (a := (u : ZMod g).val * (v : ZMod g).val) (by simp))).2 (hm _ _ hu hv) }
  refine ⟨{ S with inv_mem' := fun {u} hu => ?_ }, fun u => Iff.rfl⟩
  have : u⁻¹ ∈ Submonoid.powers u := mem_powers_iff_mem_zpowers.2 (inv_mem (Subgroup.mem_zpowers u))
  exact (Submonoid.powers_le (P := S)).2 hu this

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) : A.ker a ↔ A.ker b := by
  unfold AbF.ker
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h]

private theorem pm_iff (n a : ℕ) : (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

private theorem jac_congr {a b q : ℕ} (h : a ≡ b [MOD q]) : jacobiSym (a : ℤ) q = jacobiSym (b : ℤ) q :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.2 h)

theorem UpperTheory.V.Chr.abLevel :
    (∀ (A : AbF) (E : Type) [Field E] [NumberField E], IsAbField A E → HasLevel E A.m A.H) ∧
          ∀ (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E], IsCompField A e q d E → ∀ (N : ℕ) [NeZero N], 2 ^ (e + 2) ∣ N → A.m ∣ N → q ∣ N → d ∣ N →
            ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H ∧ ∀ (u : (ZMod N)ˣ) (a : ℕ), (u : ZMod N) = (a : ZMod N) →
              (u ∈ H ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧ jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1) := by
  refine ⟨?_, ?_⟩
  · rintro A E _ _ ⟨N, _, j, ζ, h, hζ, hj⟩
    refine down A.ker A.m (fun a b => ker_congr A) A.H (fun u => ?_) E N h j ζ hζ hj
    unfold AbF.ker
    rw [ZMod.natCast_zmod_val]
    exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, e⟩ => Units.ext e ▸ hv⟩
  · rintro A e q d E _ _ ⟨M, _, j, ζ, a1, a2, a3, a4, hζ, hj⟩ N _ b1 b2 b3 b4
    haveI : NeZero (Nat.gcd M N) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'⟩
    let P : ℕ → Prop := fun a => (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
    have hP : ∀ a b, a ≡ b [MOD Nat.gcd M N] → (P a ↔ P b) := fun a b h => by
      simp only [P]
      rw [pm_iff, pm_iff, (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (Nat.dvd_gcd a1 b1)),
        ker_congr A (h.of_dvd (Nat.dvd_gcd a2 b2)), jac_congr (h.of_dvd (Nat.dvd_gcd a3 b3)),
        jac_congr (h.of_dvd (Nat.dvd_gcd a4 b4))]
    have h1 : P 1 := ⟨Or.inl (Nat.ModEq.refl _), ⟨1, A.H.one_mem, by simp⟩, by simp, by simp⟩
    have hm : ∀ a b, P a → P b → P (a * b) := by
      rintro a b ⟨p1, ⟨u, hu, eu⟩, p3, p4⟩ ⟨r1, ⟨v, hv, ev⟩, r3, r4⟩
      refine ⟨?_, ⟨u * v, A.H.mul_mem hu hv, by rw [Units.val_mul, eu, ev, Nat.cast_mul]⟩, ?_, ?_⟩
      · rw [pm_iff] at p1 r1 ⊢
        rw [Nat.cast_mul]
        rcases p1 with p | p <;> rcases r1 with r | r <;> simp [p, r]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p3, r3, mul_one]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p4, r4, mul_one]
    obtain ⟨K, hK⟩ := exists_sub P _ hP h1 hm
    have hL := down P _ hP K hK E M (Nat.gcd_dvd_left M N) j ζ hζ hj
    refine ⟨_, ((levChange E N).2 _ (Nat.gcd_dvd_right M N) K).1 hL, fun u a hu => ?_⟩
    rw [Subgroup.mem_comap, hK]
    exact hP _ _ ((unitsMap_val _ u).trans ((val_modEq hu).of_dvd (Nat.gcd_dvd_right M N)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr.DecompositionCyclotomic

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h := Nat.prime_iff_prime_int.mp hl.out
  have he : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [he, MulEquiv.prime_iff]
  exact h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  unfold normV
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (vQ l).asIdeal := by
    show _ = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)})
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have e : (𝓞 ℚ ⧸ (vQ l).asIdeal) ≃+* ZMod l :=
    (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]
  simp

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  have h := A.valuation_le_one (n : A)
  simpa using h

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  have hlp : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  constructor
  · intro h
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x,
      (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply x)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA m]
  simp

end UpperTheory.V.Chr.DecompositionCyclotomic

private theorem decomposition_cyclotomic_of_mem_dec {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation x ≤ 1 → A.valuation (τ x) ≤ 1 := by
  intro hx
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  open scoped Pointwise in
    (have h1 := MulAction.mem_stabilizer_iff.mp hτ
     rw [← h1, ← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]
     exact Set.smul_mem_smul_set hx)

private theorem decomposition_cyclotomic_of_mem_dec_second {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  constructor
  · intro h
    have h' := decomposition_cyclotomic_of_mem_dec A τ⁻¹ ((Dec (F := ℚ) A).inv_mem hτ) _ h
    simpa [AlgEquiv.aut_inv] using h'
  · exact decomposition_cyclotomic_of_mem_dec A τ hτ x

private theorem decomposition_cyclotomic_of_mem_dec_third {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ z : Ω, A.valuation z < 1 ↔ z = 0 ∨ (A.valuation z ≤ 1 ∧ ¬ A.valuation z⁻¹ ≤ 1) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hv0 : A.valuation z ≠ 0 := by simpa using hz
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← lt_iff_le_not_ge]
      simp [hz]
  rw [key, key, ← map_inv₀ τ x, decomposition_cyclotomic_of_mem_dec_second A τ hτ, decomposition_cyclotomic_of_mem_dec_second A τ hτ, EmbeddingLike.map_eq_zero_iff]

open UpperTheory.V.Chr.DecompositionCyclotomic in
theorem UpperTheory.V.Chr.decCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 →
          ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ Ine (F := ℚ) A ≤ Dec (F := ℚ) A ∧
          ∃ γ ∈ Dec (F := ℚ) A, Dec (F := ℚ) A ≤ (Subgroup.zpowers γ ⊔ Ine (F := ℚ) A).topologicalClosure ∧
            ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
  intro Ω _ _ _ p A hp hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hPO := isPlaceOver_vQ (l := p) A hA
  obtain ⟨σ, hσ⟩ := exists_isFrob hPO
  have hσD : σ ∈ Dec (F := ℚ) A := hσ.1
  refine ⟨?_, Ine_le_Dec A, σ, hσD, ?_, ?_⟩
  · constructor
    rintro ⟨i, hiD⟩ hi ⟨τ, hτ⟩
    rw [Subgroup.mem_subgroupOf] at hi ⊢
    have hi2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (i x - x) < 1 := hi.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(Dec (F := ℚ) A).mul_mem ((Dec (F := ℚ) A).mul_mem hτ hiD) ((Dec (F := ℚ) A).inv_mem hτ), ?_⟩
    intro x hx
    have hτi : τ⁻¹ ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).inv_mem hτ
    have hy : A.valuation (τ⁻¹ x) ≤ 1 := decomposition_cyclotomic_of_mem_dec A τ⁻¹ hτi x hx
    have h3 := hi2 _ hy
    have heq : (τ * i * τ⁻¹) x - x = τ (i (τ⁻¹ x) - τ⁻¹ x) := by
      simp [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv]
    rw [heq, decomposition_cyclotomic_of_mem_dec_third A τ hτ]
    exact h3
  · set K := (Subgroup.zpowers σ ⊔ Ine (F := ℚ) A).topologicalClosure with hK
    have hKc : IsClosed (K : Set (G ℚ Ω)) := Subgroup.isClosed_topologicalClosure _
    have hcs := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K, hKc⟩
    refine le_trans ?_ hcs.ge
    refine le_sInf fun N hN => ?_
    have hKN : K ≤ N := hN.2
    exact Kum.decGen ℚ Ω A (vQ p) σ N hPO hσ hN.1
      (le_trans (le_sup_right.trans (Subgroup.le_topologicalClosure _)) hKN)
      (hKN (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))))
  · intro l _ hlp
    have hnot : ((l : ℕ) : 𝓞 ℚ) ∉ (vQ p).asIdeal := by
      intro h
      have h' := (intCast_mem_vQ (l := p) (l : ℤ)).mp (by simpa using h)
      rw [Int.natCast_dvd_natCast] at h'
      exact hlp ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp h').symm
    rw [cycZ_of_isFrob hnot hPO hσ, normV_vQ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactorGS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.factorGS :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G k Ω →* Oˣ), (cls k Ω N).ker ≤ ψ.ker →
          ∀ S : Set (HeightOneSpectrum (𝓞 k)), S = Above k (l * N) →
          ∃ θ : GS Ω S →* Oˣ, θ.comp (toGS Ω S) = (Psi l e ψ)⁻¹ ∧ ContAction (twist₂ l θ) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ N _ e ψ hker S hS
  have hψopen : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hker (clsFacts k Ω N).1
  have hcyc : IsClosed ((cycZ k Ω l).ker : Set (G k Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (contTw k Ω l).1
  have hNS : NS Ω S ≤ ψ.ker ⊓ (cycZ k Ω l).ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_of_isOpen _ hψopen).inter hcyc)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    have hvS : v ∉ Above k (l * N) := by
      rw [← hS]
      exact hv
    have hmem : ∀ m : ℕ, m ∣ l * N → ¬ A.valuation (m : Ω) < 1 := by
      intro m hm hlt
      apply hvS
      have hx := (hA (m : 𝓞 k)).1 (by simpa using hlt)
      obtain ⟨c, hc⟩ := hm
      show ((l * N : ℕ) : 𝓞 k) ∈ v.asIdeal
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hx
    refine ⟨?_, ?_⟩
    · exact hker ((clsFacts k Ω N).2.2.2.2 A (hmem N (dvd_mul_left N l)) hσ)
    · exact (places k Ω l A).2.2.2 (hmem l (dvd_mul_right l N)) hσ
  have hP : NS Ω S ≤ (Psi l e ψ)⁻¹.ker := by
    intro σ hσ
    have h1 : ψ σ = 1 := (hNS hσ).1
    have h2 : cycZ k Ω l σ = 1 := (hNS hσ).2
    rw [MonoidHom.mem_ker]
    unfold Psi chiO
    simp [h1, h2]
  refine ⟨QuotientGroup.lift (NS Ω S) (Psi l e ψ)⁻¹ hP, MonoidHom.ext fun σ => rfl, ?_⟩
  have heq : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
    unfold Psi
    rw [mul_inv, mul_comm, zpow_neg]
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    convert hψopen using 2
    ext σ
    simp
  have hG := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  rw [← heq] at hG
  unfold ReciprocityTheory.Gal.ContAction at hG ⊢
  rw [← ((QuotientGroup.isOpenQuotientMap_mk (N := NS Ω S)).prodMap (IsOpenQuotientMap.id (X := QO l O))).continuous_comp_iff]
  exact hG
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LayerLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem UpperTheory.V.Chr.layerLevel_emb (n : ℕ) [NeZero n] (K L C : Type) [Field K] [Field L] [Field C] [Algebra K L]
    [Algebra K C] [IsCyclotomicExtension {n} K L] (ζ : C) (hζ : IsPrimitiveRoot ζ n) : Nonempty (L →ₐ[K] C) := by
  haveI : Polynomial.IsSplittingField K L (Polynomial.X ^ n - 1) :=
    IsCyclotomicExtension.isSplittingField_X_pow_sub_one (n := n) (K := K) (L := L)
  have hs : Polynomial.Splits ((Polynomial.X ^ n - 1 : Polynomial K).map (algebraMap K C)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
      ← Polynomial.C_1]
    exact Polynomial.X_pow_sub_one_splits hζ
  exact ⟨Polynomial.IsSplittingField.lift L _ hs⟩

theorem UpperTheory.V.Chr.layerLevel :
    ∀ (A : AbF) (l j : ℕ), l.Prime → ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
          IsAbField A L₀ → IsLayer l j L₀ L₁ → ∃ (N : ℕ) (_ : NeZero N) (H : Subgroup (ZMod N)ˣ), HasLevel L₁ N H := by
  intro A l j hl L₀ _ _ L₁ _ _ _ hA hL
  obtain ⟨N, hN, jj, ζ, -, hζ, -⟩ := hA
  obtain ⟨⟨k, hk⟩, -⟩ := hL
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI hN' : NeZero (N * l ^ k) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (((N * l ^ k : ℕ)) : ℚ) := ⟨by exact_mod_cast NeZero.ne (N * l ^ k)⟩
  obtain ⟨r, hr⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot {N * l ^ k} ℚ
    (CyclotomicField (N * l ^ k) ℚ) _ _ _ (CyclotomicField.isCyclotomicExtension (N * l ^ k) ℚ)
    (N * l ^ k) rfl (NeZero.ne _)
  have hrN : IsPrimitiveRoot (r ^ (l ^ k)) N := by
    have h0 := hr.pow_of_dvd (pow_ne_zero k hl.ne_zero) (dvd_mul_left _ N)
    rwa [Nat.mul_div_cancel _ (pow_pos hl.pos k)] at h0
  have hrl : IsPrimitiveRoot (r ^ N) (l ^ k) := by
    have h0 := hr.pow_of_dvd (NeZero.ne N) (dvd_mul_right N _)
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))] at h0
  obtain ⟨g⟩ := @layerLevel_emb N _ ℚ (CyclotomicField N ℚ) (CyclotomicField (N * l ^ k) ℚ)
    _ _ _ _ _ (CyclotomicField.isCyclotomicExtension N ℚ) _ hrN
  letI : Algebra L₀ (CyclotomicField (N * l ^ k) ℚ) :=
    ((g : CyclotomicField N ℚ →+* CyclotomicField (N * l ^ k) ℚ).comp
      (jj : L₀ →+* CyclotomicField N ℚ)).toAlgebra
  obtain ⟨h1⟩ := layerLevel_emb (l ^ k) L₀ L₁ (CyclotomicField (N * l ^ k) ℚ) (r ^ N) hrl
  obtain ⟨H, hH⟩ := (levChange L₁ (N * l ^ k)).1
    ⟨(h1 : L₁ →+* CyclotomicField (N * l ^ k) ℚ).toRatAlgHom⟩
  exact ⟨N * l ^ k, hN', H, hH⟩
end

