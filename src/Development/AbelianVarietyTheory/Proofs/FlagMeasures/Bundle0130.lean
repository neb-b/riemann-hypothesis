module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalSpanOfLatticeAtPlaceEqForAlmostAllPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section Global

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_zsmul_mem_of_span (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℤ, c ≠ 0 ∧ c • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIsIntegral.exists_int_smul_mem ..)

theorem exists_zsmul_le (L M : Submodule (𝓞 E) (Fin n → E)) (hL : Module.Finite (𝓞 E) L)
    (hM : Submodule.span E (M : Set (Fin n → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ L, c • x ∈ M := by
  obtain ⟨S, hS⟩ : L.FG := Module.Finite.iff_fg.mp hL
  have hfin : ∀ T : Finset (Fin n → E), ∃ c : ℤ, c ≠ 0 ∧ ∀ x ∈ T, c • x ∈ M := by
    classical
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a T _ ih =>
      obtain ⟨c, hc, hcT⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_zsmul_mem_of_span M hM a
      refine ⟨d * c, mul_ne_zero hd hc, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_comm, mul_smul]
        exact zsmul_mem hda c
      · rw [mul_smul]
        exact zsmul_mem (hcT x hx) d
  obtain ⟨c, hc, hcS⟩ := hfin S
  refine ⟨c, hc, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcS x hx
  | zero => simp
  | add a b _ _ ha hb =>
    rw [smul_add]
    exact M.add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact M.smul_mem a hy

end Global

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_inv_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) (c : ℤ)
    (hv : (c : 𝓞 F) ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (c : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
    have h2 : (c : F) = algebraMap (𝓞 F) F (c : 𝓞 F) := by simp
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)
    rw [h3, h2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem loc_le_of_zsmul (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (c : ℤ)
    (hc : c ≠ 0) (hv : (c : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, c • x ∈ M) : loc v L ≤ loc v M := by
  have hu := int_inv_mem_adicCompletionIntegers v c hv
  set u : v.adicCompletion F := (algebraMap F (v.adicCompletion F) (c : F))⁻¹ with hudef
  have hne : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hc
  have hs : (1 : E) ⊗ₜ[F] u ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  have hgen : (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) ∈ loc (F := F) v M :=
    Submodule.subset_span ⟨c • x, h x hx, rfl⟩
  have hm := (loc (F := F) v M).smul_mem ⟨_, hs⟩ hgen
  suffices heq : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) =
      (⟨(1 : E) ⊗ₜ[F] u, hs⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) ((c • x) i)) by
    show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc (F := F) v M
    rw [heq]
    exact hm
  funext i
  have hci : (c • x) i = (c : F) • x i := by
    simp [Int.cast_smul_eq_zsmul]
  have hone : (c : F) • u = 1 := by
    rw [Algebra.smul_def, hudef, mul_inv_cancel₀ hne]
  show (x i) ⊗ₜ[F] (1 : v.adicCompletion F) = ((1 : E) ⊗ₜ[F] u) * ((c • x) i ⊗ₜ[F] (1 : v.adicCompletion F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, hci, one_mul, mul_one, TensorProduct.smul_tmul, hone]

end Local

theorem loc_eq_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M →
    {v : HeightOneSpectrum (𝓞 F) | loc v L ≠ loc v M}.Finite := by
  intro F E _ _ _ _ _ n L M hL hM
  obtain ⟨c, hc, hcLM⟩ := exists_zsmul_le L M hL.1 hM.2
  obtain ⟨d, hd, hdML⟩ := exists_zsmul_le M L hM.1 hL.2
  have hcd : (((c * d : ℤ) : 𝓞 F)) ≠ 0 := by
    exact_mod_cast mul_ne_zero hc hd
  have hI : Ideal.span {(((c * d : ℤ) : 𝓞 F))} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hcd
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  by_contra hn
  have hcv : (c : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  have hdv : (d : 𝓞 F) ∉ v.asIdeal := fun h => hn (by
    rw [Int.cast_mul]
    exact Ideal.mul_mem_left _ _ h)
  exact hv (le_antisymm (loc_le_of_zsmul v L M c hc hcv hcLM) (loc_le_of_zsmul v M L d hd hdv hdML))

end GlobalTheory.St.G

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
section
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

def resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A : ∀ i, Subgroup (G i)) :
    Subgroup (∀ i, G i) where
  carrier := {g | {i | g i ∉ A i}.Finite}
  one_mem' := by
    have : {i | (1 : ∀ i, G i) i ∉ A i} = ∅ := by
      ext i; simp [one_mem]
    simp only [Set.mem_setOf_eq, this, Set.finite_empty]
  mul_mem' := by
    intro a b ha hb
    refine (Set.Finite.union ha hb).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (mul_mem h.1 h.2)
  inv_mem' := by
    intro a ha
    refine Set.Finite.subset ha (fun i hi => ?_)
    simpa using hi

theorem pi_le_resPi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (A U : ∀ i, Subgroup (G i))
    (h : {i | A i ≠ U i}.Finite) : Subgroup.pi Set.univ U ≤ resPi A := by
  intro g hg
  refine Set.Finite.subset h (fun i hi hAU => hi ?_)
  rw [hAU]
  exact hg i (Set.mem_univ i)

theorem exists_finset_cosets {G : Type} [Group G] (K L : Subgroup G) (h : L.relIndex K ≠ 0) :
    ∃ T : Finset G, ∀ k ∈ K, ∃ t ∈ T, t⁻¹ * k ∈ L := by
  haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : G)), ?_⟩
  intro k hk
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨k, hk⟩)), ?_⟩
  have h1 : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K ⧸ L.subgroupOf K) : K) :
      K ⧸ L.subgroupOf K) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.1 h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem double_cosets_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : K0.relIndex KA ≠ 0)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ KA, g = γ * a * κ) :
    ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
  obtain ⟨S, hS⟩ := hS
  obtain ⟨T, hT⟩ := exists_finset_cosets KA K0 h
  refine ⟨Finset.image₂ (· * ·) S T, fun g => ?_⟩
  obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
  obtain ⟨t, ht, htκ⟩ := hT κ hκ
  exact ⟨a * t, Finset.mem_image₂_of_mem ha ht, γ, hγ, t⁻¹ * κ, htκ, by group⟩

theorem finite_conj_transfer {G : Type} [Group G] (Γ KA K0 : Subgroup G)
    (h : KA.relIndex K0 ≠ 0) (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ KA}.Finite) (a : G) :
    {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
  obtain ⟨T, hT⟩ := exists_finset_cosets K0 KA h
  have hpiece : ∀ t ∈ T, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ * a) ∈ KA}.Finite := by
    intro t _
    by_cases hne : ∃ γ₀, γ₀ ∈ Γ ∧ a⁻¹ * γ₀ * a ∈ K0 ∧ t⁻¹ * (a⁻¹ * γ₀ * a) ∈ KA
    · obtain ⟨γ₀, hγ₀, -, h₀⟩ := hne
      refine ((hF a).image (fun δ => γ₀ * δ)).subset ?_
      rintro γ ⟨hγ, -, h₁⟩
      refine ⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, ?_⟩, by group⟩
      have := KA.mul_mem (KA.inv_mem h₀) h₁
      convert this using 1
      group
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨h1, h2, h3⟩
      exact hne ⟨γ, h1, h2, h3⟩
  refine (T.finite_toSet.biUnion hpiece).subset ?_
  rintro γ ⟨hγ, hk⟩
  obtain ⟨t, ht, htk⟩ := hT _ hk
  exact Set.mem_biUnion ht ⟨hγ, hk, htk⟩

theorem invVol_subgroupOf {G : Type} [Group G] (R K L : Subgroup G) (hK : K ≤ R) (hL : L ≤ R) :
    invVol (K.subgroupOf R) (L.subgroupOf R) = invVol K L := by
  simp only [invVol, Subgroup.relIndex_subgroupOf hK, Subgroup.relIndex_subgroupOf hL]

theorem tsum_quot_out {Y : Type} (r : Y → Y → Prop) (s : Setoid Y) (hr : ∀ a b, r a b ↔ s.r a b)
    (F : Y → ℝ≥0∞) : ∑' o : Quot r, F o.out = ∑' o : Quotient s, F o.out := by
  obtain rfl : r = s.r := by
    funext a b
    exact propext (hr a b)
  rfl

theorem stabilizer_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] {X : ι → Type}
    [∀ i, MulAction (G i) (X i)] (x : ∀ i, X i) :
    MulAction.stabilizer (∀ i, G i) x =
      Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_pi, funext_iff]

theorem stabilizer_res {P : Type} [Group P] (R : Subgroup P) {Y : Type} [MulAction P Y] (y : Y) :
    MulAction.stabilizer R y = (MulAction.stabilizer P y).subgroupOf R := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]

end GlobalTheory.HL

namespace GlobalTheory.HL

theorem mass_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  intro ι G _ X _ A H _ φ hinj hres hdc hfin x0 hcomm hae
  set R := resPi A with hRdef
  let φ' : H →* R := φ.codRestrict R hres
  have hφ' : ∀ h, ((φ' h : R) : ∀ i, G i) = φ h := fun h => rfl
  set Γ : Subgroup R := φ'.range with hΓ
  set KA : Subgroup R := (Subgroup.pi Set.univ A).subgroupOf R with hKA
  set K0 : Subgroup R := MulAction.stabilizer R x0 with hK0
  have hAR : Subgroup.pi Set.univ A ≤ R := pi_le_resPi A A (by simp)
  have hstab0 : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i)) ≤ R :=
    pi_le_resPi A _ hae
  have hK0' : K0 = (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x0 i))).subgroupOf R := by
    rw [hK0, stabilizer_res, stabilizer_pi]
  have hpi := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i)) A
    (by simpa [eq_comm] using hae) hcomm
  have hc1 : K0.relIndex KA ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hAR]; exact hpi.1
  have hc2 : KA.relIndex K0 ≠ 0 := by
    rw [hK0', hKA, Subgroup.relIndex_subgroupOf hstab0]; exact hpi.2.1
  have hDC : ∃ S : Finset R, ∀ g : R, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ := by
    refine double_cosets_transfer Γ KA K0 hc1 ?_
    obtain ⟨S, hSR, hS⟩ := hdc
    refine ⟨S.subtype (· ∈ R), fun g => ?_⟩
    obtain ⟨s, hs, h, k, hk, hg⟩ := hS g g.2
    have hkR : k ∈ R := hAR (fun i _ => hk i)
    refine ⟨⟨s, hSR s hs⟩, by simpa using hs, φ' h, ⟨h, rfl⟩, ⟨k, hkR⟩, ?_, ?_⟩
    · simpa [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi] using hk
    · ext1; simpa [hφ'] using hg
  have hFin : ∀ a : R, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite := by
    refine finite_conj_transfer Γ KA K0 hc2 (fun a => ?_)
    refine ((hfin a a.2).image φ').subset ?_
    rintro γ ⟨⟨h, rfl⟩, hγ⟩
    refine ⟨h, fun i => ?_, rfl⟩
    have := hγ
    simp only [hKA, Subgroup.mem_subgroupOf, Subgroup.mem_pi, Set.mem_univ, forall_const] at this
    simpa [hφ'] using this i
  obtain ⟨V0, hV0, hmass⟩ := _root_.GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets Γ K0 hDC hFin
  refine ⟨V0, hV0, fun x hx hxae => ?_⟩

  have hAx : {i | A i ≠ MulAction.stabilizer (G i) (x i)}.Finite := by
    refine (hae.union hxae).subset (fun i hi => ?_)
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hi (by rw [h.1, h.2])
  have hstabx : Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i)) ≤ R :=
    pi_le_resPi A _ hAx
  have hSx : MulAction.stabilizer R x =
      (Subgroup.pi Set.univ (fun i => MulAction.stabilizer (G i) (x i))).subgroupOf R := by
    rw [stabilizer_res, stabilizer_pi]
  have hpx := invVol_pi_univ (fun i => MulAction.stabilizer (G i) (x0 i))
    (fun i => MulAction.stabilizer (G i) (x i))
    (hxae.subset (fun i hi h => hi (by rw [h]))) hx
  have d1 : K0.relIndex (MulAction.stabilizer R x) ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstabx]; exact hpx.1
  have d2 : (MulAction.stabilizer R x).relIndex K0 ≠ 0 := by
    rw [hK0', hSx, Subgroup.relIndex_subgroupOf hstab0]; exact hpx.2.1
  have hm := hmass (∀ i, X i) x d1 d2
  have hvol : invVol K0 (MulAction.stabilizer R x) =
      ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i)) := by
    rw [hK0', hSx, invVol_subgroupOf R _ _ hstab0 hstabx]; exact hpx.2.2
  rw [← hvol, ← hm]
  have hφinj : Function.Injective φ' := fun a b hab => hinj (congrArg Subtype.val hab)
  have horb : ∀ y : ∀ i, X i, ((∀ i, ∃ g : G i, g • x i = y i) ∧ {i | y i ≠ x i}.Finite) ↔
      y ∈ MulAction.orbit R x := by
    intro y
    constructor
    · rintro ⟨hall, hf⟩
      let g : ∀ i, G i := fun i => if y i = x i then 1 else Classical.choose (hall i)
      have hgR : g ∈ R := by
        refine hf.subset (fun i hi hyx => hi ?_)
        simp only [g, hyx, if_true]
        exact one_mem _
      refine ⟨⟨g, hgR⟩, funext fun i => ?_⟩
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      by_cases hyx : y i = x i
      · simp [g, hyx]
      · simp only [g, hyx, if_false]
        exact Classical.choose_spec (hall i)
    · rintro ⟨g, rfl⟩
      refine ⟨fun i => ⟨(g : ∀ i, G i) i, by dsimp only; rw [Subgroup.smul_def, Pi.smul_apply']⟩, ?_⟩
      refine ((g.2 : {i | (g : ∀ i, G i) i ∉ A i}.Finite).union hAx).subset (fun i hi => ?_)
      by_contra h
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
      apply hi
      dsimp only
      rw [Subgroup.smul_def, Pi.smul_apply']
      have := h.1
      rw [h.2] at this
      exact this
  have henc : ∀ y : ∀ i, X i, {h : H | φ h • y = y}.encard =
      ((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard := by
    intro y
    rw [← hφinj.encard_image]
    congr 1
    ext γ
    simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
      MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, rfl⟩, by rw [Subgroup.smul_def]; exact hh⟩
    · rintro ⟨⟨h, rfl⟩, hh⟩
      exact ⟨h, by rw [Subgroup.smul_def] at hh; exact hh, rfl⟩
  refine (tsum_congr fun o => ?_).trans (tsum_quot_out _ (MulAction.orbitRel Γ (∀ i, X i)) ?_ (fun y =>
    if y ∈ MulAction.orbit R x then
      ((((Γ ⊓ MulAction.stabilizer R y : Subgroup R) : Set R).encard : ℝ≥0∞))⁻¹ else 0))
  · beta_reduce
    simp only [henc, horb]
  · intro a b
    rw [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨φ' h, h, rfl⟩⁻¹, ?_⟩
      dsimp only
      simp [Subgroup.smul_def, hφ']
    · rintro ⟨⟨γ, h, rfl⟩, hγ⟩
      refine ⟨h⁻¹, ?_⟩
      rw [← hγ]
      dsimp only
      simp [Subgroup.smul_def, hφ']

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroDefectHeightPowerAbsorbsConstants
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NonzeroDefect

theorem num_first (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) :
    2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 1)) ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have h1 : q ^ (-((k : ℤ) - 1)) ≤ q ^ (-((k : ℤ) - 2 * r - 5)) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have hq0 : 0 < q := by linarith
  gcongr
  norm_num

theorem num_second (H q : ℝ) (hq : 2 ≤ q) (hH : 0 ≤ H) (r k : ℕ) (hk : 4 * r + 7 ≤ k) :
    98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) *
        (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤
      98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))) * q ^ (-((k : ℤ) - 2 * r - 5)) := by
  have hq0 : 0 < q := by linarith
  have h1 : (q ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2 ≤ q ^ (-((k : ℤ) - 2 * r - 5)) := by
    rw [← zpow_natCast, ← zpow_mul]
    exact zpow_le_zpow_right₀ (by linarith) (by push_cast; omega)
  gcongr

theorem nonzeroDefect_height_power_absorbs_constants (H : ℝ) (hH : 2 ≤ H) (r : ℕ) :
    H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1)))) ≤
      H ^ (39 * (r + 1) ^ 2) := by
  have h0 : 0 < H := by linarith
  have h9 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by gcongr
  calc H ^ (2 * (r + 2)) * (98 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * H ^ (4 * (r + 1))))
      = 392 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by ring
    _ ≤ H ^ 9 * (H ^ (2 * (r + 2)) * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * H ^ (4 * (r + 1))) := by gcongr
    _ = H ^ (9 + (2 * (r + 2) + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1))) := by
        simp only [pow_add H]
    _ ≤ H ^ (39 * (r + 1) ^ 2) := pow_le_pow_right₀ (by linarith) (by nlinarith [Nat.zero_le r])

theorem ampSq_nonzero_defect : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → (S.ampSq fun d Λ => ¬ S.BBzero d Λ) ≤ ENNReal.ofReal (S.Hp ^ (39 * (r + 1) ^ 2) * (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ ¬ S.BBzero d Λ
  · obtain ⟨d, Λ, hT, hB⟩ := hex
    have hq : (2 : ℝ) ≤ (S.q : ℝ) := by
      have := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
      exact_mod_cast this
    have hqH : (S.q : ℝ) ≤ S.Hp := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.2.2.1 hB
    have hH : (2 : ℝ) ≤ S.Hp := hq.trans hqH
    have hH0 : (0 : ℝ) ≤ S.Hp := by linarith
    have hq0 : (0 : ℝ) < (S.q : ℝ) := by linarith
    have key := _root_.GlobalTheory.HL.TypesCS.ampSq_le_of_types L r k S hk
      (ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) *
        (S.q : ℝ) ^ (-((k : ℤ) - 2 * r - 5))) * S.nn)
      (fun β => (_root_.GlobalTheory.HL.FirstType.first_type_bound L r k S hk β).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_first _ _ hq hH0 r k)) _))
      (fun β J βJ => (_root_.GlobalTheory.HL.FamilyBound.family_bound L r k S hk β J βJ).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (num_second _ _ hq hH0 r k hk)) _))
    refine key.trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul_of_nonneg_right (nonzeroDefect_height_power_absorbs_constants _ hH r) (by positivity)
  · have h0 : (S.ampSq fun d Λ => ¬ S.BBzero d Λ) = 0 := by
      have ha : ∀ d, S.amp d (fun Λ => ¬ S.BBzero d Λ) = 0 := by
        intro d
        unfold Frames.amp
        have : ∀ Λ, ¬ (S.IsTerm d Λ ∧ ¬ S.BBzero d Λ) := fun Λ h => hex ⟨d, Λ, h⟩
        simp only [this, if_false, tsum_zero]
      unfold Frames.ampSq Frames.sumData
      simp [ha]
    rw [h0]
    exact zero_le

end GlobalTheory.HL.NonzeroDefect
end

