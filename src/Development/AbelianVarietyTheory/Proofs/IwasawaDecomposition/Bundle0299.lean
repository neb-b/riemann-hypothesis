module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFiel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat


open GlobalTheory.Mem.Col2.TC.PsiRat in
theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLatticeStepZeroAddConjGeneratorDualSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem base_sup_dual_eq {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n : ℕ}
    (Lb M : Submodule (𝓞 E) (Fin n → E)) (π pb : 𝓞 E) (hpb : (pb : E) = σ (π : E))
    (hspan : Submodule.span E (Lb : Set (Fin n → E)) = ⊤)
    (hL : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r))
    (hM : ∀ x, x ∈ M ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range) :
    Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) = M := by
  have hform1 : ∀ x y : Fin n → E, hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      refine (hM x).2 fun j => ?_
      obtain ⟨r, hr, -⟩ := (hL x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.ideal_span_singleton_smul]
      rintro _ ⟨y, hy, rfl⟩
      simp only [DistribSMul.toLinearMap_apply]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        refine (hM _).2 fun j => ?_
        by_cases hj : j.1 + 1 = n
        · have hx : Pi.single j (π : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨π, by simp, fun _ => dvd_rfl⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simpa [Algebra.smul_def, hpb] using this
        · have hx : Pi.single j (1 : E) ∈ Lb := by
            refine (hL _).2 fun i => ?_
            by_cases h : i = j
            · subst h
              exact ⟨1, by simp, fun hi => absurd hi hj⟩
            · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
          have := hy _ hx
          rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
          simp only [Pi.single_eq_same, map_one, one_mul] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨pb * r, by simp [Algebra.smul_def, hr]⟩
      | zero => simp
      | add y z _ _ h1 h2 => rw [smul_add]; exact M.add_mem h1 h2
      | smul c y _ h => rw [smul_comm]; exact M.smul_mem c h
  · intro x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (le_sup_left : Lb ≤ _) ((hL x).2 fun j => j.elim0)
    have hxi := (hM x).1 hx
    let l : Fin n := ⟨n - 1, by omega⟩
    have hl : l.1 + 1 = n := by simp [l]; omega
    have hπ : π ≠ 0 := by
      rintro rfl
      have hle : Submodule.span E (Lb : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) l) := by
        refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
        have : r = 0 := zero_dvd_iff.1 (hd hl)
        simp [hr, this]
      rw [hspan] at hle
      have := hle (Submodule.mem_top (x := Pi.single l (1 : E)))
      simp at this
    have hpb0 : (pb : E) ≠ 0 := by
      rw [hpb]
      intro h
      exact hπ (by simpa using (map_eq_zero σ).1 h)
    obtain ⟨t, ht⟩ := hxi l
    have hy : Pi.single l (x l / (pb : E)) ∈ dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb := by
      intro z hz
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]
      obtain ⟨r, hr, hd⟩ := (hL z).1 hz l
      obtain ⟨s, rfl⟩ := hd hl
      obtain ⟨w, hw⟩ := hσO s
      refine ⟨w * t, ?_⟩
      rw [map_mul, hw, ht, hr, Pi.single_eq_same]
      simp only [map_mul, ← hpb]
      rw [← ht]
      field_simp
    have hx' : Function.update x l 0 ∈ Lb := by
      refine (hL _).2 fun j => ?_
      by_cases h : j = l
      · subst h
        exact ⟨0, by simp, fun _ => dvd_zero _⟩
      · obtain ⟨r, hr⟩ := hxi j
        refine ⟨r, by simp [h, hr], fun hj => absurd (Fin.ext (by simp [l]; omega)) h⟩
    have hx'' : Pi.single l (x l) ∈ Ideal.span {pb} • Submodule.span (𝓞 E) (dualSet σ (1 : Matrix (Fin n) (Fin n) E) Lb) := by
      rw [Submodule.ideal_span_singleton_smul]
      refine ⟨_, Submodule.subset_span hy, ?_⟩
      funext j
      by_cases h : j = l
      · subst h
        simp [Algebra.smul_def, mul_div_cancel₀ _ hpb0]
      · simp [h]
    refine Submodule.mem_sup.2 ⟨_, hx', _, hx'', ?_⟩
    funext j
    by_cases h : j = l
    · subst h
      simp
    · simp [h]

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem base_step_zero_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (pb : 𝓞 (I.rec7 l Z).host.E), (pb : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj ((A u).piU : (I.rec7 l Z).host.E) → (H.lev0 u).Lb ⊔ Ideal.span {pb} • Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet ((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (I.rec7 l Z).sp.gram0 (H.lev0 u).Lb) = (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
  intro B X I hI hP l Z H F A hS hH hT u pb hpb
  obtain ⟨-, -, -, hN⟩ := _root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgram, hl0, -⟩ := hN 0 (Nat.zero_le _)
  have hgram0 : (I.rec7 l Z).sp.gram0 = 1 := by
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun hgram (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)) (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b)
    have e : (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a = Fin.cast (rank_eq_first_level (I.rec7 l Z).R) b) ↔ a = b := by simp [Fin.ext_iff]
    simp only [Matrix.one_apply, e] at this
    rw [Matrix.one_apply]
    exact this
  rw [hgram0]
  obtain ⟨k, hk⟩ := (hS u).1.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb := (hH.car0 u).Lb_eq
  have hπ : (A u).piU = X.piT u := (hT.piU u).symm.trans (hS u).1.piU
  refine base_sup_dual_eq _ _ _ (X.piT u) pb ?_ (H.lev0 u).Lb_span ?_ ?_
  · have e := congrArg (fun t : 𝓞 B.host.E => (t : B.host.E)) hπ
    exact hpb.trans ((congrArg (I.rec7 l Z).host.conj e).trans (Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj (I.rec7 l Z) _).symm)
  · intro x
    have e1 : x ∈ (H.lev0 u).Lb ↔ reV (rank_eq_first_level (I.rec7 l Z).R) _ x ∈ ((F u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb := by
      rw [hLb]
      constructor
      · exact fun h => ⟨x, h, rfl⟩
      · rintro ⟨y, hy, e⟩
        have : y = x := (reV (rank_eq_first_level (I.rec7 l Z).R) _).injective e
        exact this ▸ hy
    refine e1.trans ((hk.lb () _).trans ?_)
    constructor
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _))⟩
    · intro h j
      obtain ⟨r, hr, hd⟩ := h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
      exact ⟨r, hr, fun hj => hd (hj.trans (rank_eq_first_level _).symm)⟩
  · intro x
    have e1 : (fun j => x (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)) ∈ selfDualLatticeCoords (I.rec7 l Z) 0 (Nat.zero_le _) ↔
        x ∈ (I.rec7 l Z).sp.crdLat0 ((I.rec7 l Z).sp.X 0).L0 := by
      constructor
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext a
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) a)
      · rintro ⟨v, hv, e⟩
        refine ⟨v, hv, ?_⟩
        funext j
        exact congrFun e (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)
    refine e1.symm.trans ((hl0 _).trans ?_)
    exact ⟨fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R) j), fun h j => h (Fin.cast (rank_eq_first_level (I.rec7 l Z).R).symm j)⟩

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGenerator
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem isClosed_singleton_of_isAdic {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (c : O) :
    IsClosed ({c} : Set O) := by
  have e : ({c} : Set O) = ⋂ M : ℕ, (fun x => x - c) ⁻¹'
      ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro rfl M
      simp
    · intro h
      have h2 := Ideal.mem_iInf.2 h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
      simpa [sub_eq_zero] using h2
  rw [e]
  refine isClosed_iInter fun M => IsClosed.preimage (continuous_id.sub continuous_const) ?_
  exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ M : Ideal O).toAddSubgroup
    ((isAdic_iff.1 had).1 M)

theorem joint_pow_of_tameGen : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  intro E Ω _ _ _ _ _ A γ hγ O _ _ _ _ _ had χ hχ m hm0 hm hI e π hπ he
  set q : Ω := γ π / π with hqdef
  have hroot : ∀ τ : G E Ω, (τ π / π) ^ m = 1 := by
    intro τ
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hq : q ^ m = 1 := hroot γ
  have hc : χ γ ^ m = 1 := hI γ hγ.1
  have hinv : ∀ {M : Type} [Group M] (x : M), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro M _ x hx n
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_add, show n * (m - 1) + n = n * m by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [Nat.mul_add]]
    rw [pow_mul', hx, one_pow]
  have hinv0 : ∀ (x : Ω), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro x hx n
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0.ne'] at hx
      exact zero_ne_one hx
    have := hinv (Units.mk0 x hx0) (by ext; simpa using hx) n
    have := congrArg (fun u : Ωˣ => (u : Ω)) this
    simpa using this
  let H : Subgroup (G E Ω) :=
    { carrier := {σ | σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = q ^ n}
      mul_mem' := by
        rintro σ τ ⟨hσ, n₁, h₁, h₁'⟩ ⟨hτ, n₂, h₂, h₂'⟩
        refine ⟨mul_mem hσ hτ, n₁ + n₂, ?_, ?_⟩
        · rw [map_mul, h₁, h₂, pow_add]
        · rw [quot_mul hσ m hm hπ he, h₁', h₂', pow_add]
      one_mem' := ⟨one_mem _, 0, by simp, by simp [div_self hπ]⟩
      inv_mem' := by
        rintro σ ⟨hσ, n, h₁, h₁'⟩
        have hσi : σ⁻¹ ∈ Ine (F := E) A := inv_mem hσ
        refine ⟨hσi, n * (m - 1), ?_, ?_⟩
        · rw [map_inv, h₁, hinv _ hc]
        · have h3 := quot_mul hσi m hm hπ he (τ := σ)
          rw [inv_mul_cancel, AlgEquiv.one_apply, div_self hπ, h₁'] at h3
          rw [← hinv0 q hq, eq_inv_of_mul_eq_one_left h3.symm] }
  have hclosed : IsClosed (H : Set (G E Ω)) := by
    have e : (H : Set (G E Ω)) = (Ine (F := E) A : Set (G E Ω)) ∩
        ⋃ n ∈ Finset.range m, ({σ : G E Ω | ((χ σ : Oˣ) : O) = ((χ γ ^ n : Oˣ) : O)} ∩
          {σ : G E Ω | σ π = q ^ n * π}) := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hσ, n, h₁, h₁'⟩
        refine ⟨hσ, n % m, Nat.mod_lt _ hm0, ?_, ?_⟩
        · rw [h₁, ← pow_mod_orderOf, ← pow_mod_orderOf (χ γ) (n % m)]
          congr 2
          have hd := orderOf_dvd_of_pow_eq_one hc
          rw [Nat.mod_mod_of_dvd _ hd]
        · rw [← pow_mod_orderOf, ← div_eq_iff hπ, h₁']
          rw [← pow_mod_orderOf q n]
          congr 1
          rw [Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hq)]
      · rintro ⟨hσ, n, -, h₁, h₁'⟩
        exact ⟨hσ, n, Units.ext h₁, by rw [h₁', mul_div_cancel_right₀ _ hπ]⟩
    rw [e]
    refine (isClosed_Ine A).inter (isClosed_biUnion_finset fun n _ => IsClosed.inter ?_ ?_)
    · exact (isClosed_singleton_of_isAdic had _).preimage hχ
    · exact isClosed_setOf_apply π (fun y => y = q ^ n * π)
  intro σ hσ
  have hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro τ (rfl | hτ)
    · exact ⟨hγ.1, 1, by simp, by simp [hqdef]⟩
    · have hτI : τ ∈ Ine (F := E) A := GlobalTheory.TameGenPowers.wild_mem_Ine hτ
      refine ⟨hτI, 0, ?_, ?_⟩
      · rw [pow_zero]
        exact GlobalTheory.WildSetSQ.char_eq_one_of_wild A had χ hχ τ hτ m hm (hI τ hτI)
      · rw [pow_zero]
        exact eq_one_of_pow_eq_one A hm (hroot τ) (hτ π hπ)
  have hmem := closure_minimal (SetLike.coe_subset_coe.2 hle) hclosed (hγ.2 hσ)
  exact hmem.2

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyCoeffCongrSamePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem eventually_map_residue_eq {Γ O : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)) {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) O) (hM : Continuous M) (g0 : Γ) :
    ∀ᶠ g in nhds g0, (M g).map (IsLocalRing.residue O) = (M g0).map (IsLocalRing.residue O) := by
  have h : ∀ a b, ∀ᶠ g in nhds g0, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    intro a b
    have hc : Continuous fun g => M g a b - M g0 a b := (hM.matrix_elem a b).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds (by simp))
  have h2 : ∀ᶠ g in nhds g0, ∀ a b, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; exact h a
  filter_upwards [h2] with g hg
  ext a b
  simp only [Matrix.map_apply]
  exact (Ideal.Quotient.eq).2 (hg a b)

theorem sub_mem_nonunits_vs {K : Type} [Field K] (A : ValuationSubring K) {x y : K}
    (hx : x ∈ A.nonunits) (hy : y ∈ A.nonunits) : x - y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  exact lt_of_le_of_lt (A.valuation.map_sub x y) (max_lt hx hy)

theorem charpoly_coeff_congr_same_place : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  classical
  intro D Rw Pl X Y hCheb hRw hPl σ i i' hw Sig Sig' ρ ρ' hP hR hP' hR' g n
  have key : ∀ (j : X.nd.Loc) (y y' : X.nd.O j), IsLocalRing.residue (X.nd.O j) y = IsLocalRing.residue (X.nd.O j) y' →
      iotaO X.nd Y.naut j y - iotaO X.nd Y.naut j y' ∈ (Pl.plB (X.nd.w j)).nonunits := by
    intro j y y' hyy
    obtain ⟨h1, e1⟩ := hPl j y
    obtain ⟨h2, e2⟩ := hPl j y'
    have hres : IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h1⟩ = IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h2⟩ := by
      apply (Pl.plκ (X.nd.w j)).injective
      apply (fbCast (X.nd.w_l j) (D.what₂.places.resChar_prime (X.nd.w j)) (X.nd.lPrime j).out).injective
      rw [e1, e2, hyy]
    have hm := (Ideal.Quotient.eq).1 hres
    have hv := (ValuationSubring.valuation_lt_one_iff _ _).1 hm
    rw [ValuationSubring.mem_nonunits_iff]
    simpa using hv
  have key' := key i'
  rw [← hw] at key'
  have hO : ∀ j, IsOpen ((IsLocalRing.maximalIdeal (X.nd.O j) : Ideal (X.nd.O j)) : Set (X.nd.O j)) := fun j => by
    simpa using (isAdic_iff.1 (X.nd.O_adic j)).1 1
  have hclosed : IsClosed {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g0 hg0
    have e1 := eventually_map_residue_eq (hO i) (fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i))) hR.1 g0
    have e2 := eventually_map_residue_eq (hO i') (fun g => (ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i'))) hR'.1 g0
    filter_upwards [e1, e2] with g h1 h2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hg0 ⊢
    intro hg
    apply hg0
    have c1 : IsLocalRing.residue (X.nd.O i) ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i) ((ρ g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h1]
    have c2 : IsLocalRing.residue (X.nd.O i') ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i') ((ρ' g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h2]
    have := sub_mem_nonunits_vs _ hg (sub_mem_nonunits_vs _ (key i _ _ c1) (key' _ _ c2))
    convert this using 1
    ring
  have hfin := Filter.eventually_cofinite.1 hR.2.2
  have hfin' := Filter.eventually_cofinite.1 hR'.2.2
  have hdense := hCheb (hfin.toFinset ∪ hfin'.toFinset)
  have hE := hdense.mono (s₂ := {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits}) (fun s hs => by
    obtain ⟨w, hwS, hsplit, B, hB, hF⟩ := hs
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hwS
    obtain ⟨q1, q2⟩ := hwS
    have r1 := q1 B s hB hF
    have r2 := q2 B s hB hF
    have eqloc : isoLoc X.nd Y.naut Sig w = isoLoc X.nd Y.naut Sig' w :=
      (hP.2.2 w hsplit).trans ((hRw i σ w).trans ((hRw i' σ w).symm.trans (hP'.2.2 w hsplit).symm))
    rw [Set.mem_setOf_eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, r1, r2, eqloc, sub_self, ValuationSubring.mem_nonunits_iff,
      map_zero]
    exact zero_lt_one)
  have hc := hE.closure_eq
  rw [hclosed.closure_eq] at hc
  exact Set.eq_univ_iff_forall.1 hc g

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlongStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_om_heisO_along_eq_integral_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ ξ, IsoVec T ξ → ∀ (μ : Measure (ZI T ξ)) (𝓕 : Set (ZI T ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ T).subgroupOf (ZI T ξ)) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a, ∫ z in 𝓕, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ a) f) 0 ∂μ = ∫ z in 𝓕, om (1, (z : GA D T)) f 0 ∂μ := by
  first | exact @GlobalTheory.TransvConst.constantTerm_heisO_along | exact GlobalTheory.TransvConst.constantTerm_heisO_along | (intros; apply GlobalTheory.TransvConst.constantTerm_heisO_along <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.dtTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ T : Formalism.L2.Host.DtTied (I.rec7 l Z) (I.cf l Z), ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
  intro B X I _ _ l Z
  refine ⟨GlobalTheory.Mem.Col2.dtIsoRational (I.rec7 l Z) (I.cf l Z) I.SQ (MulEquiv.refl _) (fun j => rfl) rfl ?_ (fun z => rfl), fun _ => rfl⟩
  show UOQ B.host I.SQ = _
  ext x
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPointStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end

