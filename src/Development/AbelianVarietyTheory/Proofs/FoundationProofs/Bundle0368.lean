module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem htPresNu7_mono_loss : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (c : Coef l)
  (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₂ c' : ℕ) (ζ : Ω) (ι : Type) [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l),
  HTPresNuOfPolys A c m c₂ Z ζ P o → c₂ ≤ c' → HTPresNuOfPolys A c m c' Z ζ P o := by
  intro l _ Ω _ _ _ A c Z m c₂ c' ζ ι _ P o h hc
  obtain ⟨hζ, hco, hoO, hne, hK⟩ := h
  obtain ⟨hζ₂, -, hu, ho, hs⟩ := hK
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    have : NeZero ((l ^ i : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hl.pos i).ne'⟩
    infer_instance
  set n' := m - c' with hn'
  set d := (m - c₂) - n' with hd
  have hdn : d + n' = m - c₂ := by omega
  have hpow : (ζ ^ l ^ c₂) ^ l ^ d = ζ ^ l ^ c' := by
    rw [← pow_mul, ← pow_add]
    rcases Nat.lt_or_ge m c' with h | h
    swap
    · congr 2; omega
    · have e1 : m ≤ c₂ + d := by omega
      rw [(hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l e1), (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow l h.le)]
  have hζ' : IsPrimitiveRoot (ζ ^ l ^ c') (l ^ n') := by
    rw [← hpow]
    exact hζ₂.pow (pow_pos hl.pos _) (by rw [← pow_add, hdn])
  refine ⟨hζ, hco, hoO, hne, hζ', by omega, hu, ho, ?_⟩
  intro s hsI hcyc _
  have hfix : s (ζ ^ l ^ c₂) = ζ ^ l ^ c₂ := by
    refine GlobalTheory.Col.fix_of_cycMod (le_refl m) hcyc ?_
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  obtain ⟨k, hkv, hcg⟩ := hs s hsI hcyc hfix
  refine ⟨fun i => ((k i).val : ZMod (l ^ n')), fun i => ?_, ?_⟩
  · obtain ⟨v, hv, hsv⟩ := hkv i
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, hdn, hv], ?_⟩
    rw [ZMod.val_natCast, map_pow, hsv, mul_pow, ← pow_mul, mul_comm (k i).val, pow_mul, hpow,
      ← pow_eq_pow_mod _ hζ'.pow_eq_one]
  · have hN : ∀ a : ℕ, ‖(a : Qbar l)‖ ≤ 1 := fun a => IsUltrametricDist.norm_natCast_le_one _ a
    have key : ∀ i, ‖o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      intro i
      have e : (((k i).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (((k i).val / l ^ n' : ℕ) : Qbar l) + (((k i).val % l ^ n' : ℕ) : Qbar l) := by
        exact_mod_cast (Nat.div_add_mod (k i).val (l ^ n')).symm
      have e2 : o i * ((k i).val : Qbar l) - o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l) =
          ((l : ℕ) : Qbar l) ^ n' * (o i * (((k i).val / l ^ n' : ℕ) : Qbar l)) := by
        rw [ZMod.val_natCast]
        linear_combination (o i) * e
      rw [e2, norm_mul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (ho i) (norm_nonneg _) (hN _))
    have h1 : ‖Z m s 1 - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
      refine le_trans hcg ?_
      rw [norm_pow, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (hN l) (by omega)
    have h2 : ‖∑ i, (o i * ((k i).val : Qbar l) -
        o i * ((((k i).val : ZMod (l ^ n')).val : ℕ) : Qbar l))‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => key i)
    have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
    rw [Finset.sum_sub_distrib, sub_add_sub_cancel] at h3
    exact h3

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaFieldUnram

theorem valuation_eq_zpow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k :=
  GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed

end GlobalTheory.InertiaFieldUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernelStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_inertia_cyclotomic_kernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω) (m : ℕ), IsClosed ((Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
  first | exact @GlobalTheory.isClosed_Ine_inf_ker_cycMod | exact GlobalTheory.isClosed_Ine_inf_ker_cycMod | (intros; apply GlobalTheory.isClosed_Ine_inf_ker_cycMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalDualityCharacterOrthogonalClasses
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.localDuality_char : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' a b : G ℚ Ω → Qbar l), OverL l A → ContinuousOn k (Dec (F := ℚ) A) → ContinuousOn k' (Dec (F := ℚ) A) → ContinuousOn a (Dec (F := ℚ) A) → ContinuousOn b (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ a s ∈ c.O ∧ b s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t ∧ k' (s * t) = k' s * k' t ∧ b (s * t) = b s + k s * b t ∧ a (s * t) = a s + k' s * a t) → (∃ s ∈ Dec (F := ℚ) A, k s ≠ 1) → (∃ s ∈ Dec (F := ℚ) A, k' s ≠ 1) → (∀ n : ℕ, Cob2 c n (Dec (F := ℚ) A) (fun s t => b s * (k' s * a t))) → (∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, b s = k s * x - x) ∨ ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x := by
  intro hL l _ Ω _ _ _ c A k k' a b hA hk hk' ha hb hint hmul hk1 hk'1 hcob
  by_cases hac : ∃ x : Qbar l, ∀ s ∈ Dec (F := ℚ) A, a s = k' s * x - x
  · exact Or.inr hac
  left
  obtain ⟨θ, hθc, hθ⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k k' hk
    (fun s hs => ⟨(hint s hs).1, (hint s hs).2.1, (hint s hs).2.2.2.2⟩) (fun s hs t ht => (hmul s hs t ht).1)
  obtain ⟨θ', hθ'c, hθ'⟩ := GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product l Ω c A k' k hk'
    (fun s hs => ⟨(hint s hs).2.1, (hint s hs).1, by rw [mul_comm]; exact (hint s hs).2.2.2.2⟩)
    (fun s hs t ht => (hmul s hs t ht).2.1)
  have hN := _root_.GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c
  have hchi : ∀ s : G ℚ Ω, ((((UpperTheory.V.Base.chiO ℚ Ω l c.O) s : c.Oˣ) : c.O) : Qbar l) = eps l s := by
    intro s; rfl
  have hcyc : θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype := by
    refine MonoidHom.ext fun g => Units.ext (Subtype.ext ?_)
    simp only [MonoidHom.mul_apply, Units.val_mul, Subalgebra.coe_mul, hθ, hθ', MonoidHom.comp_apply,
      Subgroup.coe_subtype, hchi]
    exact (hint g g.2).2.2.2.2
  have hθ1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'1 : ∃ g, θ' g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := hk'1
    exact ⟨⟨s, hs⟩, fun h => hne (by have e := hθ' ⟨s, hs⟩; rw [h] at e; exact e.symm.trans rfl)⟩
  have hθ'ne : ∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hk1
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have e := DFunLike.congr_fun hcyc ⟨s, hs⟩
    rw [MonoidHom.mul_apply, ← h] at e
    have e1 : θ ⟨s, hs⟩ = 1 := mul_eq_right.1 e
    have e2 := hθ ⟨s, hs⟩; rw [e1] at e2; exact e2.symm.trans rfl
  set p : c.O := ((l : ℕ) : c.O) with hp
  let aO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨a s, (hint s.1 s.2).2.2.1⟩
  let bO : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨b s, (hint s.1 s.2).2.2.2.1⟩
  have haO : Continuous aO := (continuousOn_iff_continuous_domRestrict.1 ha).subtype_mk _
  have hbO : Continuous bO := (continuousOn_iff_continuous_domRestrict.1 hb).subtype_mk _
  have haOc : ∀ s t, aO (s * t) = aO s + ((θ' s : c.Oˣ) : c.O) * aO t := fun s t => Subtype.ext (by
    simp only [aO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ']
    exact (hmul s.1 s.2 t.1 t.2).2.2.2)
  have hbOc : ∀ s t, bO (s * t) = bO s + ((θ s : c.Oˣ) : c.O) * bO t := fun s t => Subtype.ext (by
    simp only [bO, Subalgebra.coe_add, Subalgebra.coe_mul, hθ]
    exact (hmul s.1 s.2 t.1 t.2).2.2.1)
  have hnorm1 : ∀ x : c.O, ‖((x : c.O) : Qbar l)‖ ≤ 1 := fun x => by
    have := (hN 0 x).2 (by simp); simpa using this
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocCharAnn.exists_depth_of_not_coboundary l (Set.univ : Set ↥(Dec (F := ℚ) A)) (fun s => k' s) (fun s => a s)
    (by obtain ⟨s, hs, hne⟩ := hk'1; exact ⟨⟨s, hs⟩, trivial, hne⟩)
    (fun ⟨X, hX⟩ => hac ⟨X, fun s hs => hX ⟨s, hs⟩ trivial⟩)
  have hann : ∀ n : ℕ, ∀ x y : c.O, (∀ s, p ^ n ∣ x * aO s - (((θ' s : c.Oˣ) : c.O) * y - y)) → p ^ (n - r) ∣ x := by
    intro n x y h
    refine (hN (n - r) x).1 (hr n x y (hnorm1 x) fun s _ => ?_)
    have := (hN n _).2 (h s)
    simpa [aO, hθ'] using this
  obtain ⟨m, hm0, hAF⟩ := GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow hL.lf hL.lt hL.le l Ω c A hA θ' hθ'c hθ'1 hθ'ne r
  have key : ∀ n : ℕ, 1 ≤ n → ∃ x : c.O, ∀ s, p ^ n ∣ (m : c.O) * bO s - (((θ s : c.Oˣ) : c.O) * x - x) := by
    intro n hn
    refine GlobalTheory.T.coboundary_of_orthogonal_dualCharacter_modPrimePow hL.lf hL.lt l Ω c A hA θ θ' hθc hθ'c hcyc n hn (fun s => (m : c.O) * bO s)
      (continuous_const.mul hbO) (fun s t => ?_) (fun a' ha' hca' => ?_)
    · rw [hbOc s t]; ring_nf; exact dvd_zero _
    obtain ⟨x, y, hxy⟩ := hAF n hn aO haO (fun s t => by rw [haOc s t, sub_self]; exact dvd_zero _)
      (hann n) a' ha' hca'
    obtain ⟨u, huc, huO, hu⟩ := hcob n
    let u0 : ↥(Dec (F := ℚ) A) → c.O := fun s => ⟨u s, huO s⟩
    have hu0c : Continuous u0 := (continuousOn_iff_continuous_domRestrict.1 huc).subtype_mk _
    have hu0 : ∀ s t, p ^ n ∣ bO s * (((θ' s : c.Oˣ) : c.O) * aO t) -
        ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u0 t - u0 (s * t) + u0 s) := by
      intro s t
      refine (hN n _).1 ?_
      have e : ‖b s.1 * (k' s.1 * a t.1) - (eps l s.1 * u t.1 - u (s.1 * t.1) + u s.1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
        hu s.1 s.2 t.1 t.2
      have he : k s.1 * k' s.1 = eps l s.1 := (hint s.1 s.2).2.2.2.2
      rw [← he] at e
      convert e using 2
      simp only [aO, bO, u0, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, hθ, hθ']
      rfl
    have hbt : Continuous (fun s => bO s * ((θ' s : c.Oˣ) : c.O)) := hbO.mul hθ'c
    have hcu : Continuous (fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y) :=
      (continuous_const.mul hu0c).sub (hbt.mul continuous_const)
    refine ⟨fun s => x * u0 s - bO s * ((θ' s : c.Oˣ) : c.O) * y, hcu, fun s t => ?_⟩
    obtain ⟨q1, hq1⟩ := hxy t
    obtain ⟨q2, hq2⟩ := hu0 s t
    refine ⟨bO s * ((θ' s : c.Oˣ) : c.O) * q1 + x * q2, ?_⟩
    simp only []
    rw [hbOc s t, map_mul θ' s t, Units.val_mul]
    linear_combination (bO s * ((θ' s : c.Oˣ) : c.O)) * hq1 + x * hq2
  obtain ⟨s0, hs0, hne0⟩ := hk1
  refine GlobalTheory.T.coboundary_of_uniform_limit_coboundaries (Dec (F := ℚ) A : Set (G ℚ Ω)) k b ⟨s0, hs0, hne0⟩ fun ε hε => ?_
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hm : (0 : ℝ) < ‖((m : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hm0.ne')
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hm) hl1
  obtain ⟨x, hx⟩ := key (n + 1) (Nat.le_add_left 1 n)
  refine ⟨(x : Qbar l) / (m : Qbar l), fun s hs => ?_⟩
  have e := (hN (n + 1) _).2 (hx ⟨s, hs⟩)
  have e2 : ((((m : c.O) * bO ⟨s, hs⟩ - (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) * x - x) : c.O)) : Qbar l) =
      (m : Qbar l) * (b s - (k s * ((x : Qbar l) / (m : Qbar l)) - (x : Qbar l) / (m : Qbar l))) := by
    have hm' : (m : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
    have hb' : ((bO ⟨s, hs⟩ : c.O) : Qbar l) = b s := rfl
    have hk'' : (((θ ⟨s, hs⟩ : c.Oˣ) : c.O) : Qbar l) = k s := hθ _
    push_cast [hb', hk'']
    field_simp
  rw [e2, norm_mul] at e
  have e3 : ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ n := by
    rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)
  rw [← le_div_iff₀' hm] at e
  refine e.trans ?_
  rw [div_le_iff₀ hm]
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) → (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (a (n + 1) s) (a n s)) → (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) → (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) → (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) → (¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y)) → ¬ GrZero W A := by
  first | exact @GlobalTheory.Ord2.limit_nonzero_ordinary_class | exact GlobalTheory.Ord2.limit_nonzero_ordinary_class | (intros; apply GlobalTheory.Ord2.limit_nonzero_ordinary_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPower
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp

theorem norm_gSum_le : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)),
    z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  intro l _ m z ψ hz
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = m - k := ⟨_, rfl⟩
  rw [← hk]
  have hsm : s ≤ m := by omega
  have hmss : m ≤ s + s := by omega
  have hmsk : m = s + k := by omega
  haveI : NeZero (l ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π : ZMod (l ^ m) →+* ZMod (l ^ s) := ZMod.castHom (pow_dvd_pow l hsm) (ZMod (l ^ s))
  have hsurj : Function.Surjective π := ZMod.castHom_surjective (pow_dvd_pow l hsm)
  let q : ZMod (l ^ m) := ((l ^ s : ℕ) : ZMod (l ^ m))
  have hqq : q * q = 0 := by
    simp only [q, ← Nat.cast_mul, ← pow_add, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l hmss
  have hπq : π q = 0 := by
    simp only [q]
    rw [map_natCast, ZMod.natCast_self]
  have hfib : ∀ x x0 : ZMod (l ^ m), π x = π x0 → ∃ y, x = x0 + q * y := by
    intro x x0 h
    have h0 : π (x - x0) = 0 := by rw [map_sub, h, sub_self]
    have hd : ((x - x0).val : ZMod (l ^ m)) = x - x0 := ZMod.natCast_zmod_val _
    rw [← hd, map_natCast, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨j, hj⟩ := h0
    refine ⟨(j : ZMod (l ^ m)), ?_⟩
    rw [← sub_eq_iff_eq_add', ← hd, hj, Nat.cast_mul]
  let e : ZMod (l ^ m) → Qbar l := fun x => z ^ x.val
  have he : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    simp only [e, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hz).symm
  let g : ZMod (l ^ m) → Qbar l := fun x => ψ x * e x
  have hzn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    simp only [g, e, norm_mul, norm_pow, hzn, one_pow, mul_one]
    exact DirichletCharacter.norm_le_one ψ x
  have hsum : gSum m z ψ = ∑ x, g x := by
    unfold gSum
    symm
    rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun x _ hx => by
      by_contra h; exact hx (by simp [g, MulChar.map_nonunit ψ h]))]
    refine Finset.sum_bij' (fun x hx => (Finset.mem_filter.1 hx).2.unit) (fun b _ => (b : ZMod (l ^ m)))
      ?_ ?_ ?_ ?_ ?_ <;> simp [g, e]
  have hmove : ∀ x x0 y : ZMod (l ^ m), π x = π x0 → x * q * y = x0 * q * y := by
    intro x x0 y h
    obtain ⟨y', rfl⟩ := hfib x x0 h
    linear_combination (y' * y) * hqq
  have h1 : ∀ y : ZMod (l ^ m), (1 - q * y) * (1 + q * y) = 1 := fun y => by
    linear_combination (-(y * y)) * hqq
  have hinv : ∀ x0 y : ZMod (l ^ m), ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x =
      ψ (1 + q * y) * e (x0 * q * y) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x := by
    intro x0 y
    rw [Finset.mul_sum]
    calc ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x
        = ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g (x * (1 + q * y)) := by
          refine Finset.sum_nbij' (fun x => x * (1 - q * y)) (fun x => x * (1 + q * y)) ?_ ?_ ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_sub, map_one, hπq,
              zero_mul, sub_zero, mul_one] at ha ⊢
            exact ha
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_add (f := _), map_one, hπq,
              zero_mul, add_zero, mul_one] at ha ⊢
            exact ha
          · intro a _
            simp only [mul_assoc, h1, mul_one]
          · intro a _
            simp only [mul_assoc, mul_comm (1 + q * y), h1, mul_one]
          · intro a _
            simp only [mul_assoc, h1, mul_one]
      _ = _ := Finset.sum_congr rfl fun x hx => by
          have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
          show ψ (x * (1 + q * y)) * e (x * (1 + q * y)) = ψ (1 + q * y) * e (x0 * q * y) * (ψ x * e x)
          rw [map_mul, show x * (1 + q * y) = x + x * q * y by ring, he, hmove x x0 y hx']
          ring
  have H : ∀ u w y' : ZMod (l ^ m), IsUnit u → w = u + q * y' →
      (∀ y, ψ (1 + q * y) * e (u * q * y) = 1) → g w = g u := by
    intro u w y' hu hw hχu
    obtain ⟨U, rfl⟩ := hu
    have hUU : (U : ZMod (l ^ m)) * ((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = 1 := Units.mul_inv U
    have hw' : w = (U : ZMod (l ^ m)) + U * q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y') := by
      rw [hw]; linear_combination (-(q * y')) * hUU
    have hw'' : w = (U : ZMod (l ^ m)) * (1 + q * (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')) := by
      rw [hw']; ring
    have := hχu (((U⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * y')
    show ψ w * e w = ψ U * e U
    rw [hw'', map_mul, ← hw'', hw', he]
    linear_combination (ψ U * e U) * this
  have hcard0 : ∀ x0, (Finset.univ.filter (fun x => π x = π x0)).card =
      (Finset.univ.filter (fun x => π x = 0)).card := by
    intro x0
    refine Finset.card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_sub, ha, sub_self]
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      rw [map_add (f := _), ha, zero_add]
    · intro a _; simp
    · intro a _; simp
  have htot : l ^ m = l ^ s * (Finset.univ.filter (fun x => π x = 0)).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := π)
      (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at this
    refine this.trans ?_
    rw [Finset.sum_congr rfl (g := fun _ => (Finset.univ.filter (fun x => π x = 0)).card) (fun c _ => by
      obtain ⟨x0, rfl⟩ := hsurj c
      exact hcard0 x0), Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  have hcardk : (Finset.univ.filter (fun x => π x = 0)).card = l ^ k := by
    have h2 : l ^ s * (Finset.univ.filter (fun x => π x = 0)).card = l ^ s * l ^ k := by
      rw [← htot, ← pow_add, ← hmsk]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s) h2
  rw [hsum, ← Finset.sum_fiberwise Finset.univ π g]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => ?_
  obtain ⟨x0, rfl⟩ := hsurj c
  by_cases hχ : ∀ y, ψ (1 + q * y) * e (x0 * q * y) = 1
  · have hall : ∀ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = g x0 := by
      intro x hx
      have hx' : π x = π x0 := (Finset.mem_filter.1 hx).2
      obtain ⟨y', hy'⟩ := hfib x x0 hx'
      by_cases hu0 : IsUnit x0
      · exact H x0 x y' hu0 hy' hχ
      by_cases hu : IsUnit x
      · refine (H x x0 (-y') hu (by rw [hy']; ring) fun y => ?_).symm
        rw [hmove x x0 y hx']
        exact hχ y
      · show ψ x * e x = ψ x0 * e x0
        rw [MulChar.map_nonunit ψ hu, MulChar.map_nonunit ψ hu0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, norm_mul, hcard0, hcardk]
    push_cast
    calc ‖(l : Qbar l) ^ k‖ * ‖g x0‖ ≤ ‖(l : Qbar l) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 x0) (norm_nonneg _)
      _ = _ := mul_one _
  · push_neg at hχ
    obtain ⟨y, hy⟩ := hχ
    have hI := hinv x0 y
    have h0 : ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
      have hm : (1 - ψ (1 + q * y) * e (x0 * q * y)) * ∑ x ∈ Finset.univ.filter (fun x => π x = π x0), g x = 0 := by
        rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 (Ne.symm hy))
    rw [h0, norm_zero]
    positivity

end GlobalTheory.KZ.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

theorem tau_mul_dvd (c : Coef l) (n : ℕ) (b' : c.O)
    (h : ∀ a : Qn c n, tbA c n (a * red c n b') = 0) (x : c.O) :
    ∃ q : ℤ_[l], tau c (b' * x) = (l : ℤ_[l]) ^ n * q := by
  have h1 := h (red c n x)
  rw [← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  rw [mul_comm]
  exact h1

theorem pair_nondeg (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n)
    (h : ∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) : b = 0 := by
  obtain ⟨b', rfl⟩ := red_surjective c n b
  have hd := tau_mul_dvd c n b' h
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let q : c.O → ℤ_[l] := fun x => Classical.choose (hd x)
  have hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x := fun x => Classical.choose_spec (hd x)
  let g : c.O →ₗ[ℤ_[l]] ℤ_[l] :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_add, map_add (f := _), hq, hq, mul_add]
      map_smul' := fun r x => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        ring }
  obtain ⟨a0, ha0⟩ := (tau_spec c g).exists
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := (tau c).comp (LinearMap.mulLeft ℤ_[l] b')
  have e1 : ∀ x, f x = tau c (b' * x) := fun x => rfl
  have e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x) := fun x => by
    rw [e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    exact ha0 x
  have heq : b' = ((l : ℤ_[l]) ^ n) • a0 := (tau_spec c f).unique e1 e2
  rw [heq, red_eq_zero_iff_mem]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0

end GlobalTheory.Ord2.SelPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientCharTrivialInertiaCyclotomicTowerStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_trivial_inertia_cyclotomic_tower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g → ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 → mat W s 1 1 = 1 := by
  first | exact @GlobalTheory.quot_eq_one_of_cycBar_eq_one | exact GlobalTheory.quot_eq_one_of_cycBar_eq_one | (intros; apply GlobalTheory.quot_eq_one_of_cycBar_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtensionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_cochain_cocycle_extension : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  first | exact @GlobalTheory.br_tame | exact GlobalTheory.br_tame | (intros; apply GlobalTheory.br_tame <;> assumption)
end

