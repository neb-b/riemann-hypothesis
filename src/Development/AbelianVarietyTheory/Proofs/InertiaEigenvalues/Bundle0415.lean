module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalRingPolyDividesVarPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeight
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (_root_.GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (_root_.GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finsetSum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := _root_.GlobalTheory.ExpImage.expStar_levSum LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.ExactMult

theorem finrank_add_of_exact {L A₀ A₁ A₂ : Type} [Field L] [AddCommGroup A₀] [Module L A₀]
    [AddCommGroup A₁] [Module L A₁] [AddCommGroup A₂] [Module L A₂] (i : A₀ →ₗ[L] A₁) (p : A₁ →ₗ[L] A₂)
    (hi : Function.Injective i) (hk : LinearMap.range i = LinearMap.ker p)
    (S₀ : Submodule L A₀) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂) [FiniteDimensional L S₁]
    (h0 : S₀ = S₁.comap i) (h2 : S₁.map p = S₂) :
    finrank L S₁ = finrank L S₀ + finrank L S₂ := by
  have e := LinearMap.finrank_range_add_finrank_ker (p.domRestrict S₁)
  rw [LinearMap.range_domRestrict, h2, LinearMap.ker_domRestrict, ← hk] at e
  have e1 : finrank L ((LinearMap.range i).comap S₁.subtype) = finrank L S₀ := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, h0,
      (Submodule.equivMapOfInjective i hi (S₁.comap i)).finrank_eq, Submodule.map_comap_eq, inf_comm]
  omega

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem mem_fil (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g x = x) ∧
      ∀ c : K, mulVdR (LL := LL) (V := V) c x = τ c • x) ∧ x ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]

theorem map_mul (f : V →ₗ[LL] V') (c : K) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V') c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g x) =
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, he]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem act_mul (ρ : Representation LL G V) (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem mul_mem_filV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (LL := LL) (V := V) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR, Algebra.smul_def]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz

noncomputable def ev (x : V ⊗[Qp] BdR) : LL ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun (c : LL) (k : K) => c • mulVdR (LL := LL) (V := V) k x)
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun c k k' => by
      rw [← smul_add]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR, add_mul, tmul_add]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel)
    (fun q c k => by
      rw [smul_comm q c]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : algebraMap K BdR (q • k) * b = q • (algebraMap K BdR k * b) := by
          rw [← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]
        simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, this,
          tmul_smul]
      | add y z hy hz => simp only [map_add (f := _), hy, hz, smul_add]))

theorem ev_tmul (x : V ⊗[Qp] BdR) (c : LL) (k : K) :
    ev (LL := LL) (K := K) x (c ⊗ₜ k) = c • mulVdR (LL := LL) (V := V) k x := rfl

theorem mul_mul (y k : K) (x : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) (V := V) (y * k) x = mulVdR (LL := LL) (V := V) y (mulVdR (LL := LL) (V := V) k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_fildR_eq [CharZero Qp] (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (f : V →ₗ[LL] V') (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hs : ∀ y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a,
      ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a,
        AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = y) :
    (FildR PD ρ τ a).map (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FildR PD ρ' τ a := by
  haveI := PD.finK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_fil PD ρ τ a x).1 hx
    refine (mem_fil PD ρ' τ a _).2 ⟨⟨fun g => ?_, fun c => ?_⟩, GlobalTheory.HTW.map_mem_FilV PD f a x h3⟩
    · rw [← map_act PD ρ ρ' f he, h1]
    · rw [← map_mul, h2, map_smul]
  · intro y hy
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hs y ⟨hy.1.1, hy.2⟩
    obtain ⟨⟨-, h2⟩, -⟩ := (mem_fil PD ρ' τ a _).1 hy
    have h1 : ∀ g, actVdR PD ρ g x = x := by
      simpa only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hx1
    obtain ⟨m, c, k, hc, hk⟩ := GlobalTheory.exists_embedding_idempotent_tensor Qp K LL τ
    refine ⟨∑ j, c j • mulVdR (LL := LL) (V := V) (k j) x,
      (mem_fil PD ρ τ a _).2 ⟨⟨fun g => ?_, fun y => ?_⟩, ?_⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_smul, act_mul, h1]
    · have := congrArg (ev (LL := LL) (K := K) x) (hk y)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, ev_tmul, mul_mul] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, this, Finset.smul_sum, mul_smul]
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_filV PD a _ x hx2)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, map_smul, map_mul, h2, ← mul_smul, ← Finset.sum_smul, hc, one_smul]

variable {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]

theorem tensor_exact (ι : V₀ →ₗ[LL] V) (π : V →ₗ[LL] V') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hk : LinearMap.range ι = LinearMap.ker π) :
    Function.Injective (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) ∧
      LinearMap.range (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) =
        LinearMap.ker (AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  have e1 : ∀ x, AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (ι.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have e2 : ∀ x, AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (π.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hex : Function.Exact (ι.restrictScalars Qp) (π.restrictScalars Qp) :=
    (LinearMap.exact_iff.2 hk.symm : Function.Exact ι π)
  constructor
  · intro x y h
    rw [e1, e1] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := BdR) (ι.restrictScalars Qp) hι h
  · ext x
    have := rTensor_exact BdR hex hπ x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, e1, e2]
    exact this.symm

end General

theorem exact_hodge_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  intro l _ P AI T K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hi hs hk hd
  obtain ⟨d2, hst⟩ := (GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hd
  obtain ⟨t1, t2⟩ := tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι π hi hs hk
  have hf : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) =
      finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) := by
    intro τ a
    haveI := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a).1
    exact finrank_add_of_exact _ _ t1 t2 _ _ _ (GlobalTheory.HTW.FildR_eq_comap (P.PD K) ρ₀ ρ₁ ι hi hι τ a)
      (map_fildR_eq (P.PD K) ρ₁ ρ₂ π hπ τ a (hst a))
  refine ⟨(GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hi hd, d2, fun τ a => ?_⟩
  have hm : multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a := by
    unfold multV
    rw [hf τ a, hf τ (a + 1)]
    push_cast
    ring
  refine ⟨hf τ a, hm, ?_⟩
  obtain ⟨-, n0, j0⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₀ ρ₀ τ a
  obtain ⟨-, -, j1⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a
  obtain ⟨-, n2, j2⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₂ ρ₂ τ a
  rw [j0, j1, j2, hm]
  omega

end GlobalTheory.Per.ExactMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescEqXPowSmulNablaPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.DescFalling

theorem desc_eq_X_pow_smul_nabla_pow {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (v : Vec K a ι) :
    C.desc k v = (X : K⟦X⟧) ^ k • (C.nabla ^ k) v := by
  have hX : ∀ w, C.nabla ((X : K⟦X⟧) • w) = w + (X : K⟦X⟧) • C.nabla w := fun w => by
    have h := C.leibniz (fun _ => X) w
    have e1 : ∀ u : Vec K a ι, ((fun _ => (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • u = (X : K⟦X⟧) • u :=
      fun u => rfl
    have e2 : ((fun _ => PowerSeries.derivative (R := K) (X : K⟦X⟧)) : ZMod a → K⟦X⟧) • w = w := by
      simp only [PowerSeries.derivative_X]
      exact one_smul _ w
    rw [e1, e1, e2] at h
    exact h
  have hcomm : ∀ (j : ℕ) (w : Vec K a ι),
      (C.nabla ^ j) ((X : K⟦X⟧) • C.nabla w) = (X : K⟦X⟧) • (C.nabla ^ (j + 1)) w + j • (C.nabla ^ j) w := by
    intro j
    induction j with
    | zero => intro w; simp
    | succ j ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, ih, map_add (f := _), hX, map_nsmul, pow_succ' C.nabla (j + 1),
        Module.End.mul_apply, pow_succ' C.nabla j, Module.End.mul_apply, succ_nsmul]
      abel
  induction k generalizing v with
  | zero => simp [Conn.desc_zero]
  | succ k ih =>
    rw [Conn.desc_succ, ih, Conn.N_apply, map_sub, hcomm, map_nsmul, add_sub_cancel_right, smul_smul,
      ← pow_succ]

end GlobalTheory.DescFalling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem le_one_of_mul_pow_le_one (c : ℝ) (n : ℕ) (h : ∀ t : ℝ≥0, t < 1 → c * (t : ℝ) ^ n ≤ 1) : c ≤ 1 := by
  have ht : Filter.Tendsto (fun t : ℝ≥0 => c * (t : ℝ) ^ n) (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)) (nhds (c * ((1 : ℝ≥0) : ℝ) ^ n)) :=
    ((continuous_const.mul ((NNReal.continuous_coe).pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  have h2 := le_of_tendsto ht (eventually_nhdsWithin_of_forall fun t (hti : t ∈ Set.Iio 1) => h t hti)
  simpa using h2

theorem disc_bdd_isSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  intro l _ K bk ρ hρ hρ1 y hy
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨a, ha1, ha2, ha3, -⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ hρ hρ1
  obtain ⟨-, hk2, -, -⟩ := _root_.GlobalTheory.BSP.disc_zero_one l K bk

  have hcont : ∀ (r : ℝ≥0), 0 < r → ∀ (b : ℕ → (bk.DS r →+ Disc l (0 : Wq l bk.a) 1)),
      (∀ n z, ‖b n z‖ * (r : ℝ) ^ n ≤ ‖z‖) → ∀ n, Continuous (b n) := by
    intro r hr b hb n
    refine AddMonoidHomClass.continuous_of_bound (b n) (((r : ℝ) ^ n)⁻¹) fun z => ?_
    have hp : (0 : ℝ) < (r : ℝ) ^ n := pow_pos (by exact_mod_cast hr) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb n z

  have htor : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) (0 : Wq l bk.a) 1).2.1 z
    rw [← nsmul_eq_mul, hz, norm_zero] at h
    exact norm_eq_zero.1 (by
      have := (div_eq_zero_iff.1 h.symm).resolve_right hl0.ne'
      exact this)

  have hle : ∀ n, ‖a n y‖ ≤ 1 := by
    intro n
    refine le_one_of_mul_pow_le_one _ n fun t ht => ?_
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy t ht
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨a', ha1', ha2', -, -⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ' hρ' h3
    have hRc : Continuous R := AddMonoidHomClass.continuous_of_bound R 1 fun z => (hR.norm_le z).trans (one_mul _).ge
    have e : ((a n).comp (R : bk.DS ρ' →+ bk.DS ρ)) = a' n :=
      (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ').2.2.1 _ htor _ _ ((hcont ρ hρ a ha2 n).comp hRc)
        (hcont ρ' hρ' a' ha2' n) fun x => by
          simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass, Function.comp_apply]
          rw [hR.ext x, RingHom.id_apply, ha1, ha1']
    have e2 : a n y = a' n y' := by rw [← hRy, ← e]; rfl
    rw [e2]
    calc ‖a' n y'‖ * (t : ℝ) ^ n ≤ ‖a' n y'‖ * (ρ' : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t.2 (by exact_mod_cast h1) n) (norm_nonneg _)
      _ ≤ ‖y'‖ := ha2' n y'
      _ ≤ 1 := hy'
  choose w hw using fun n => hk2 (a n y) (hle n)
  refine ⟨PowerSeries.mk w, ?_⟩
  have h0 : ‖y - toDisc l (X : bk.S) ρ (PowerSeries.mk w)‖ ≤ 0 :=
    ha3 _ 0 le_rfl fun n => by
      rw [map_sub, ha1, coeff_mk, ← hw, sub_self, norm_zero, zero_mul]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantTransitionMatrixCoverStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_transition_matrix_cover : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  first | (exact @GlobalTheory.CovTrans.transition) | (exact GlobalTheory.CovTrans.transition) | (intros; apply GlobalTheory.CovTrans.transition  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalRingPolyDividesVarPowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLocalRing_poly_divides_var_pow : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (l : O) (e w : ℕ) (ι : Type) [Fintype ι] (K : Set ι) (F : MvPolynomial ι O), IsDiscreteValuationRing.addVal O l = e → (∃ m : ι →₀ ℕ, m.degree < w + 1 ∧ (∀ q ∈ K, m q = 0) ∧ IsUnit (F.coeff m)) → ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : Finite A) (_ : Algebra O A) (t : A) (a : ι → A), (∀ x ∈ Ideal.span {l} * IsLocalRing.maximalIdeal O, algebraMap O A x = 0) ∧ t ^ (2 * (e + 1) * w + 2) = 0 ∧ algebraMap O A l * t ^ (2 * (e + 1) * w + 1) ≠ 0 ∧ (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, IsUnit (a q)) ∧ MvPolynomial.aeval (fun q => a q * t) F ∣ t ^ ((e + 1) * w) := by
  first | exact @GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring | exact GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring | (intros; apply GlobalTheory.NewPrime.LocalRing.exists_finite_local_ring <;> assumption)
end

