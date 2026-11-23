module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTwoCocycleReciprocityTrivialAtLastPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

variable {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

def zcl {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : H2 (charRep μ) :=
  Submodule.Quotient.mk ⟨zc c n S ξ i, zc_mem hμ hξ i⟩

theorem res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ) (i : Ix c) :
    resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0 := by
  obtain ⟨u, hu, huO, hcu⟩ := hcob
  unfold zcl resH2
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  refine ⟨fun g => crd c n i (u g), continuous_crd hu.domRestrict (fun g => huO _) n i, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply, restrictCocycles2_apply]
  change _ = zc c n S ξ i (((g : G ℚ Ω) : GS Ω (S : Set Pl)), ((h : G ℚ Ω) : GS Ω (S : Set Pl)))
  rw [zc_mk hξ, MonoidHom.coe_comp, Function.comp_apply, charRep_apply]
  have hμg : ((μ (locFam S Av v g) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l g : ℤ_[l]) :=
    congrArg Units.val (DFunLike.congr_fun hμ (g : G ℚ Ω))
  rw [hμg]
  have hc := (cg_iff (hξ.int g h) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g))).1
    (hcu g g.2 h h.2) i
  rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g),
    crd_sub i (algebraMap_mul_mem _ (huO h)) (huO _), crd_algebraMap_mul i _ (huO h)] at hc
  rw [hc]; rfl

theorem cob_of_res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (h0 : ∀ i, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0) :
    Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
  have hb : ∀ i, ∃ ci : Dec (F := ℚ) (Av v) → ZMod (l ^ n), Continuous ci ∧
      d1 ((charRep μ).comp (locFam S Av v)) ci =
        fun p => zc c n S ξ i (((p.1 : G ℚ Ω) : GS Ω (S : Set Pl)), ((p.2 : G ℚ Ω) : GS Ω (S : Set Pl))) := by
    intro i
    have := h0 i
    unfold zcl resH2 at this
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      separated_dvr_second_cohomology_mem] at this
    exact this
  choose ci hci hd using hb
  classical
  refine ⟨fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.domRestrict (Dec (F := ℚ) (Av v) : Set (G ℚ Ω))
        fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0) =
        fun g => lft c n (fun i => ci i g) := by
      funext g; exact dif_pos g.2
    rw [this]
    exact Continuous.comp (g := lft c n) (f := fun g i => ci i g) continuous_of_discreteTopology
      (continuous_pi fun i => hci i)
  · intro s
    dsimp only
    split_ifs
    · exact lft_mem _ _
    · exact c.O.zero_mem
  · intro s hs t ht
    dsimp only
    rw [dif_pos ht, dif_pos ((Dec (F := ℚ) (Av v)).mul_mem hs ht), dif_pos hs]
    have hm : ∀ a, lft c n a ∈ c.O := lft_mem n
    refine (cg_iff (hξ.int s t) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _))).2
      fun i => ?_
    rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _),
      crd_sub i (algebraMap_mul_mem _ (hm _)) (hm _), crd_algebraMap_mul i _ (hm _), crd_lft, crd_lft, crd_lft]
    have e := congrFun (hd i) (⟨s, hs⟩, ⟨t, ht⟩)
    rw [zc_mk hξ, d1_apply, MonoidHom.coe_comp, Function.comp_apply, charRep_apply] at e
    have hμg : ((μ (locFam S Av v ⟨s, hs⟩) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l s : ℤ_[l]) :=
      congrArg Units.val (DFunLike.congr_fun hμ s)
    rw [hμg] at e
    rw [← e]; rfl

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

theorem reciprocity : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl),
    l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S →
    (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  intro hL l _ Ω _ _ _ c n S ξ v₀ hl hS hξ hv₀ hloc B hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, continuousOn_const, fun _ => c.O.zero_mem, fun s _ t _ => ?_⟩
    unfold Cg
    simp only [mul_zero, sub_zero, add_zero, pow_zero, norm_one]
    exact norm_le_one_of_mem (hξ.int s t)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.Published.exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, hinv, hPT⟩ := hL.pt ℚ Ω l n (Or.inl hl) hn ζ hζ
  classical
  let Av : S → ValuationSubring Ω := fun v =>
    if h : v.1 = v₀ then B else Classical.choose (hloc v.1 v.2 h)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := by
    intro v
    by_cases h : v.1 = v₀
    · simp only [Av, dif_pos h]; rw [h]; exact hB
    · simp only [Av, dif_neg h]; exact (Classical.choose_spec (hloc v.1 v.2 h)).1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  have hNT := (hPT S hS Av hAv μ hμ (ZMod (l ^ n)) (charRep μ) (contAction_charRep hμ)).1
  have hres : ∀ i, resH2 (charRep μ) (locFam S Av ⟨v₀, hv₀⟩) (continuous_locFam S Av _)
      (zcl hμ hξ i) = 0 := by
    intro i
    have hsum := hNT.sum_eq_zero (zcl hμ hξ i)
    rw [Finset.sum_eq_single ⟨v₀, hv₀⟩] at hsum
    · have hinj : Function.Injective (invAt S Av μ hμ inv ⟨v₀, hv₀⟩) :=
        (hinv _ _ (hAv ⟨v₀, hv₀⟩)).1.1.comp (toMuLoc_bijective S Av μ hμ _).1
      exact hinj (by rw [hsum, map_zero])
    · intro v _ hv
      have hne : v.1 ≠ v₀ := fun h => hv (Subtype.ext h)
      have hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
        simp only [Av, dif_neg hne]; exact (Classical.choose_spec (hloc v.1 v.2 hne)).2
      rw [res_zcl_eq_zero hμ hξ Av v hcob i, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcob := cob_of_res_zcl_eq_zero hμ hξ Av ⟨v₀, hv₀⟩ hres
  have hA : Av ⟨v₀, hv₀⟩ = B := dif_pos rfl
  rw [hA] at hcob
  exact hcob

end GlobalTheory.Ord2.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCocycleOfPadicLimitOfApproxCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.LimCoc

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  rw [h]
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [this, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem ultra3 {K : Type*} [NormedField K] [IsUltrametricDist K] (a b c e : K) (ε : ℝ)
    (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) (hc : ‖c‖ ≤ ε) (he : ‖e‖ ≤ ε) :
    ‖a + b - c - e‖ ≤ ε := by
  have hsub : ∀ u v : K, ‖u‖ ≤ ε → ‖v‖ ≤ ε → ‖u - v‖ ≤ ε := fun u v hu hv => by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu (by rwa [norm_neg]))
  exact hsub _ _ (hsub _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)) hc) he

theorem mulVec_small {K : Type*} [NormedField K] [IsUltrametricDist K]
    (A : Matrix (Fin 2) (Fin 2) K) (w : Fin 2 → K) (ε : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ ε) (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hw 0)
  have key : ∀ j, ‖A i j * w j‖ ≤ ε := fun j => by
    rw [norm_mul]
    calc ‖A i j‖ * ‖w j‖ ≤ 1 * ε := mul_le_mul (hA i j) (hw j) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key 0) (key 1))

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (M : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (z : ℕ → Γ → Fin 2 → Qbar l) (y : Γ → Fin 2 → Qbar l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r s i, ‖z r s i‖ ≤ 1) → (∀ r s t i, ‖z r (s * t) i - (z r s + M s *ᵥ z r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s i, ‖y s i - z r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ s t, y (s * t) = y s + M s *ᵥ y t := by
  intro l _ Γ _ M z y hM _ hz hy s t
  funext i
  rw [← sub_eq_zero, ← norm_eq_zero]
  have hbound : ∀ r : ℕ, ‖y (s * t) i - (y s + M s *ᵥ y t) i‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ r := by
    intro r
    rw [← norm_pow]
    have hdecomp : y (s * t) i - (y s + M s *ᵥ y t) i =
        (y (s * t) i - z r (s * t) i) + (z r (s * t) i - (z r s + M s *ᵥ z r t) i)
          - (y s i - z r s i) - (M s *ᵥ (y t - z r t)) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]
      ring
    rw [hdecomp]
    exact ultra3 _ _ _ _ _ (hy r (s * t) i) (hz r s t i) (hy r s i)
      (mulVec_small (M s) (y t - z r t) _ (hM s) (fun j => by simpa using hy r t j) i)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)
  exact le_antisymm (ge_of_tendsto' hlim hbound) (norm_nonneg _)

end GlobalTheory.LimCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevelsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_h1_finite_levels : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  first | exact @GlobalTheory.LocChar.local_character_h1_bound | exact GlobalTheory.LocChar.local_character_h1_bound | (intros; apply GlobalTheory.LocChar.local_character_h1_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOverStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConditions_independent_of_place_over : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω), IsPlaceOver B w → IsPlaceOver B' w → ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  first | exact @GlobalTheory.Ord2.place_indep | exact GlobalTheory.Ord2.place_indep | (intros; apply GlobalTheory.Ord2.place_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.InertCoh

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def cob (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v}
  zero_mem' := ⟨0, fun s _ => by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    refine ⟨v + w, fun s hs => ?_⟩
    simp only [Pi.add_apply, hv s hs, hw s hs, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨v, hv⟩
    refine ⟨k • v, fun s hs => ?_⟩
    simp only [Pi.smul_apply, hv s hs, Matrix.mulVec_smul, smul_sub]

def coc (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
    ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t}
  zero_mem' := ⟨fun i => continuous_const, fun s i => c.O.zero_mem, fun s _ t _ => by simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun i => (ha1 i).add (hb1 i), fun s i => c.O.add_mem (ha2 s i) (hb2 s i), fun s hs t ht => ?_⟩
    simp only [Pi.add_apply, ha3 s hs t ht, hb3 s hs t ht, Matrix.mulVec_add]
    abel
  smul_mem' := by
    rintro k a ⟨ha1, ha2, ha3⟩
    refine ⟨fun i => ?_, fun s i => ?_, fun s hs t ht => ?_⟩
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact continuous_const.mul (ha1 i)
    · simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      exact c.O.mul_mem k.2 (ha2 s i)
    · simp only [Pi.smul_apply, ha3 s hs t ht, Matrix.mulVec_smul, smul_add]

theorem mem_cob {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ cob W c I ↔ ∃ v : Fin 2 → Qbar l, ∀ s ∈ I, z s = mat W s *ᵥ v - v := Iff.rfl

theorem mem_coc {W : R2 Ω l} {c : Coef l} {I : Subgroup (G ℚ Ω)} {z : G ℚ Ω → Fin 2 → Qbar l} :
    z ∈ coc W c I ↔ (∀ i, Continuous fun s => z s i) ∧ (∀ s i, z s i ∈ c.O) ∧
      ∀ s ∈ I, ∀ t ∈ I, z (s * t) = z s + mat W s *ᵥ z t := Iff.rfl

end GlobalTheory.InertCoh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem norm_le_one_of_isIntegral_zl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) :
    ‖(a : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_zl l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

theorem norm_unit_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (u : c.Oˣ) :
    ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem_coefO c u
  have h3 := norm_le_one_of_mem_coefO c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem mem_coefO_of_memE_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l),
    MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  intro l _ c x hE hx
  obtain ⟨k, hk⟩ := hE
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  set y : c.O := ⟨_, hk⟩ with hy
  set L : c.O := (l : c.O) ^ k with hL
  have hLval : ((L : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k := by simp [hL]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hL0 : L ≠ 0 := by
    intro h
    have : ((L : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    rw [hLval] at this
    exact pow_ne_zero k hl0 this
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  by_cases hy0 : y = 0
  · have : (l : PadicAlgCl l) ^ k * x = 0 := by
      have := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy0
      simpa [hy] using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero k hl0)
    · rw [h]; exact c.O.zero_mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ z : c.O, z ≠ 0 → ∃ n : ℕ, ‖(z : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n ∧
      ϖ ^ n ∣ z ∧ z ∣ ϖ ^ n := by
    intro z hz
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [h, Subalgebra.coe_mul, norm_mul, norm_unit_coefO, one_mul, Subalgebra.coe_pow, norm_pow]
    · exact ⟨(u : c.O), by rw [h, mul_comm]⟩
    · exact ⟨((u⁻¹ : c.Oˣ) : c.O), by rw [h, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨a, hya, hdy, -⟩ := key y hy0
  obtain ⟨b, hLb, -, hdL⟩ := key L hL0
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := norm_le_one_of_mem_coefO c ϖ
  have hϖ0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hyx : ((y : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * x := rfl
  have hLlt : ‖((L : c.O) : PadicAlgCl l)‖ < 1 := by
    rw [hLval, norm_pow, hnl]
    exact pow_lt_one₀ (by positivity) hlt1 (by omega)
  have hϖlt : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    rcases lt_or_eq_of_le hϖ1 with h | h
    · exact h
    exfalso
    rw [hLb, h, one_pow] at hLlt
    exact lt_irrefl _ hLlt
  have hab : b ≤ a := by
    have hle : ‖(ϖ : PadicAlgCl l)‖ ^ a ≤ ‖(ϖ : PadicAlgCl l)‖ ^ b := by
      rw [← hya, ← hLb, hyx, hLval, norm_mul]
      calc ‖(l : PadicAlgCl l) ^ k‖ * ‖x‖ ≤ ‖(l : PadicAlgCl l) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := mul_one _
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 hle
  have hdiv : L ∣ y := dvd_trans hdL (dvd_trans (pow_dvd_pow ϖ hab) hdy)
  obtain ⟨z, hz⟩ := hdiv
  have : (l : PadicAlgCl l) ^ k * x = (l : PadicAlgCl l) ^ k * (z : PadicAlgCl l) := by
    rw [← hyx, hz, Subalgebra.coe_mul, hLval]
  rw [mul_left_cancel₀ (pow_ne_zero k hl0) this]
  exact z.2

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MobToGQScalar
section
open GlobalTheory.KZ GlobalTheory.Ord2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V
open scoped MatrixGroups

namespace GlobalTheory.KZ

theorem Tower.kmap_refl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l) : X.kmap l (RingEquiv.refl X.K) x = x := by
  unfold Tower.kmap
  have : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map (RingEquiv.refl X.K).toMonoidHom))) =
      (LinearMap.id : Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) := by
    ext x; rfl
  rw [this, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroClassBoundedTorsion
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem exists_bound_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E] (φ : ι → E →ₗ[K] K)
    (f : E →ₗ[K] K) (hf : f ∈ Submodule.span K (Set.range φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : E) (r : ℝ), 0 ≤ r → (∀ j, ‖φ j p‖ ≤ r) → ‖f p‖ ≤ C * r := by
  first
  | exact @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span
  | (apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundOfSpan.norm_le_of_mem_span ..)

theorem exists_bound_multiplier {K Γ : Type} [NormedField K] (M : Γ → Matrix (Fin 2) (Fin 2) K) (Y : Γ → Fin 2 → K)
    (hY : ¬ ∃ x : Fin 2 → K, ∀ s, Y s = M s *ᵥ x - x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : K) (x : Fin 2 → K) (r : ℝ), 0 ≤ r →
      (∀ s i, ‖(a • Y s) i - (M s *ᵥ x - x) i‖ ≤ r) → ‖a‖ ≤ C * r := by
  let φ : Γ × Fin 2 → (K × (Fin 2 → K)) →ₗ[K] K := fun j =>
    (LinearMap.proj j.2).comp (((LinearMap.fst K K (Fin 2 → K)).smulRight (Y j.1)) -
      ((Matrix.toLin' (M j.1) - LinearMap.id).comp (LinearMap.snd K K (Fin 2 → K))))
  have hφ : ∀ s i a x, φ (s, i) (a, x) = (a • Y s) i - (M s *ᵥ x - x) i := by
    intro s i a x
    simp only [φ, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearMap.id_apply, Matrix.toLin'_apply, LinearMap.proj_apply, Pi.sub_apply]
  have hker : ⨅ j, LinearMap.ker (φ j) ≤ LinearMap.ker (LinearMap.fst K K (Fin 2 → K)) := by
    rintro ⟨a, x⟩ h
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
    simp only [LinearMap.mem_ker, LinearMap.fst_apply]
    by_contra ha
    refine hY ⟨a⁻¹ • x, fun s => ?_⟩
    have h1 : a • Y s = M s *ᵥ x - x := by
      funext i
      have := h (s, i)
      rw [hφ] at this
      exact sub_eq_zero.1 this
    rw [Matrix.mulVec_smul, ← smul_sub, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  obtain ⟨C, hC, h⟩ := exists_bound_of_mem_span φ _ (FiniteDimensional.mem_span_of_iInf_ker_le_ker hker)
  exact ⟨C, hC, fun a x r hr hb => h (a, x) r hr fun j => by rw [show j = (j.1, j.2) from rfl, hφ]; exact hb _ _⟩

theorem closed_multiplier : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (Y : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → Y ∈ Z1 (Loc.colRep W) → (∀ s i, Y s i ∈ c.O) → Y ∉ ReciprocityTheory.Gal.B1 (Loc.colRep W) → ∃ k0 : ℕ, ∀ (n : ℕ) (a : Qbar l), a ∈ c.O → Cob1 c n W ⊤ (fun s => a • Y s) → Cg n (a * ((l : ℕ) : Qbar l) ^ k0) 0 := by
  intro l hl Ω _ _ _ W c Y _ _ _ hY
  obtain ⟨C, hC, h⟩ := exists_bound_multiplier (mat W) Y (by
    rintro ⟨x, hx⟩
    refine hY ⟨x, ?_⟩
    funext s
    rw [hx s]
    simp [ReciprocityTheory.Gal.d0, Loc.colRep, Matrix.toLin'_apply])
  have hlt : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (C + 1)⁻¹ by positivity) hlt
  refine ⟨k, fun n a _ ⟨x, _, hx⟩ => ?_⟩
  have h1 := h a x _ (norm_nonneg _) fun s i => hx s (Subgroup.mem_top s) i
  unfold Cg
  rw [sub_zero, norm_mul, norm_pow _ k]
  have h2 : C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ 1 := by
    calc C * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ (C + 1) * (C + 1)⁻¹ :=
          mul_le_mul (by linarith) hk.le (by positivity) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  calc ‖a‖ * ‖((l : ℕ) : Qbar l)‖ ^ k ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ * ‖((l : ℕ) : Qbar l)‖ ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖((l : ℕ) : Qbar l) ^ n‖ * (C * ‖((l : ℕ) : Qbar l)‖ ^ k) := by ring
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2

end GlobalTheory.Ord2.GwCount
end

