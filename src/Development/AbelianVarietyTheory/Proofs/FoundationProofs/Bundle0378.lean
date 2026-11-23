module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0377
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeries
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxRootFixedFieldInertiaCyclotomicKernel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycRoots

theorem frob_cycAlg (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (x : A) (hx : x ∈ cycAlg l A) :
    ∃ y ∈ cycAlg l A, ∃ z : A, x = y ^ l + (l : A) * z := by
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hp.pos
    have hyA : y ∈ A := mem_of_pow_mem A hp.ne_zero (hy ▸ x.2)
    have e : (⟨y, hyA⟩ : A) ^ l = x := Subtype.ext (by simpa using hy)
    refine ⟨⟨y, hyA⟩, mem_cycAlg_of_pow (n := n + 1) ?_, 0, by rw [e]; ring⟩
    rw [pow_succ', pow_mul, e, hn]
  | algebraMap a =>
    obtain ⟨b, z, h⟩ := GlobalTheory.T.fixed_element_lth_power_mod l Ω A hA a
    exact ⟨algebraMap (fixA A) A b, Subalgebra.algebraMap_mem _ b, z, h⟩
  | add a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp y y'
    refine ⟨y + y', Subalgebra.add_mem _ hy hy', z + z' - y * y' * r, ?_⟩
    rw [hr]; ring
  | mul a b _ _ iha ihb =>
    obtain ⟨y, hy, z, rfl⟩ := iha
    obtain ⟨y', hy', z', rfl⟩ := ihb
    refine ⟨y * y', Subalgebra.mul_mem _ hy hy', z * y' ^ l + y ^ l * z' + (l : A) * z * z', ?_⟩
    rw [mul_pow]; ring

theorem approxRoot_fix_ineCyc : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) →
    0 < v (l : Ω) → v (l : Ω) < 1 → ApproxRoot l v (Fix Ω (ineCyc l A)) := by
  intro l _ hl2 Ω _ _ _ A hA v hv hl0 hl1
  have hp : l.Prime := Fact.out
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hF : ∀ x : A, x ∈ cycAlg l A ↔ (x : Ω) ∈ Fix Ω (ineCyc l A) := by
    intro x
    rw [GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff l Ω A hA x]
    exact ⟨fun h g => h g g.2, fun h s hs => h ⟨s, hs⟩⟩
  haveI : NeZero ((l ^ 2 : ℕ) : Ω) := ⟨by exact_mod_cast (pow_pos hp.pos 2).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 2)
  have hζA : ζ ∈ A := mem_of_pow_mem A (pow_pos hp.pos 2).ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
  have hζF : ζ ∈ Fix Ω (ineCyc l A) :=
    (hF ⟨ζ, hζA⟩).1 (mem_cycAlg_of_pow (n := 2) (Subtype.ext (by simpa using hζ.pow_eq_one)))
  set c : Ω := ζ - 1 with hc
  have hcF : c ∈ Fix Ω (ineCyc l A) := Subfield.sub_mem _ hζF (Subfield.one_mem _)
  have hequiv : v.IsEquiv A.valuation :=
    Valuation.isEquiv_iff_val_le_one.2 fun {x} => by rw [hv, A.valuation_le_one_iff]
  have hvc : v c ^ (l * (l - 1)) = v (l : Ω) := by
    have h := GlobalTheory.valuation_zeta_sub_one_pow_totient l Ω A 2 ζ (by norm_num) hζ
    rw [Nat.totient_prime_pow hp (by norm_num), ← map_pow] at h
    rw [← map_pow, hequiv.eq_iff]
    simpa using h
  have hN : l * (l - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hc0 : 0 < v c := by
    rcases (zero_le : 0 ≤ v c).eq_or_lt with h | h
    · rw [← h, zero_pow hN] at hvc; exact absurd hvc hl0.ne
    · exact h
  have hc1 : v c < 1 := by
    by_contra h
    exact absurd (hvc ▸ one_le_pow₀ (not_lt.1 h)) (not_le.2 hl1)
  have hcne : c ≠ 0 := fun h => by rw [h, map_zero] at hc0; exact lt_irrefl _ hc0
  set r : ℝ≥0 := v c ^ l with hr
  have hr0 : 0 < r := pow_pos hc0 l
  have hr1 : r < 1 := pow_lt_one₀ hc0.le hc1 hp.ne_zero
  have hlr : v (l : Ω) ≤ r * r := by
    rw [← hvc, pow_mul, ← hr, ← sq]
    exact pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  refine ⟨r, hr1, fun u hu => ?_⟩
  by_cases hu0 : u = 0
  · refine ⟨0, Subfield.zero_mem _, ?_⟩
    rw [hu0, zero_pow hp.ne_zero, sub_zero, map_zero]; exact zero_le
  have hvu : 0 < v u := (Valuation.pos_iff v).2 hu0
  obtain ⟨k, hk1, hk2⟩ := NNReal.exists_mem_Ioc_zpow hvu.ne' ((one_lt_inv₀ hr0).2 hr1)

  set d : Ω := c ^ (k + 1) with hd
  have hdF : d ∈ Fix Ω (ineCyc l A) := Subfield.zpow_mem _ hcF _
  have hdne : d ≠ 0 := zpow_ne_zero _ hcne
  have hvd : v (d ^ l) = r ^ (k + 1) := by
    rw [map_pow, hd, map_zpow₀, hr, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hrk : 0 < r ^ (k + 1) := zpow_pos hr0 _
  have h1 : v (u * d ^ l) ≤ 1 := by
    rw [map_mul, hvd]
    calc v u * r ^ (k + 1) ≤ r⁻¹ ^ (k + 1) * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk2 zero_le
      _ = 1 := by rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have h2 : r ≤ v (u * d ^ l) := by
    rw [map_mul, hvd]
    calc r = r⁻¹ ^ k * r ^ (k + 1) := by
          rw [zpow_add_one₀ hr0.ne', ← mul_assoc, ← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow, one_mul]
      _ ≤ v u * r ^ (k + 1) := mul_le_mul_of_nonneg_right hk1.le zero_le
  have hu'F : u * d ^ l ∈ Fix Ω (ineCyc l A) := Subfield.mul_mem _ hu (Subfield.pow_mem _ hdF _)
  obtain ⟨y, hy, z, e⟩ := frob_cycAlg l Ω A hA ⟨u * d ^ l, (hv _).1 h1⟩ ((hF _).2 hu'F)
  have e' : u * d ^ l = (y : Ω) ^ l + (l : Ω) * (z : Ω) := by
    simpa using congrArg (fun t : A => (t : Ω)) e
  refine ⟨(y : Ω) / d, Subfield.div_mem _ ((hF y).1 hy) hdF, ?_⟩
  have e2 : (u - ((y : Ω) / d) ^ l) * d ^ l = (l : Ω) * (z : Ω) := by
    rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdne), e']; ring
  have h3 : v (u - ((y : Ω) / d) ^ l) * r ^ (k + 1) ≤ r * v u * r ^ (k + 1) := by
    rw [← hvd, mul_assoc, ← map_mul, ← map_mul, e2, map_mul v (l : Ω)]
    calc v (l : Ω) * v (z : Ω) ≤ v (l : Ω) * 1 := mul_le_mul_of_nonneg_left ((hv _).2 z.2) zero_le
      _ = v (l : Ω) := mul_one _
      _ ≤ r * r := hlr
      _ ≤ r * v (u * d ^ l) := mul_le_mul_of_nonneg_left h2 zero_le
  exact le_of_mul_le_mul_right h3 hrk

end GlobalTheory.RecOne.CycRoots
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualSelmerClassesUnboundedOrderStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.exists_dualSelmer_classes_unbounded_order : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ¬ GrZero W A → ∃ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) ∧ ∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s) := by
  first | exact @GlobalTheory.Ord2.GwCount.dual_classes_unbounded | exact GlobalTheory.Ord2.GwCount.dual_classes_unbounded | (intros; apply GlobalTheory.Ord2.GwCount.dual_classes_unbounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProjectorNewformGaloisImage
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeProj

theorem heckeProj_newform : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) [Fact l.Prime], l ≠ 2 → g.M ∣ N → 5 ≤ N → Nat.Coprime N l → Odd k → 3 ≤ k → ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) → ∀ lamC : Letter → ℂ, (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lamC (Letter.T q) = g.a q) → lamC Letter.U = α → (∀ d : ℕ, Nat.Coprime d N → lamC (Letter.D d) = g.χ (d : ZMod g.M)) → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (ι : E ≃+* ℂ), let w := k - 2; let lam : Letter → E := fun T => ι.symm (lamC T); ∀ (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖(fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s * s') - (fun s => Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E)) (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → Matrix.trace (ρ s : Matrix (Fin 2) (Fin 2) E) = lam (Letter.T q) ∧ Matrix.det (ρ s : Matrix (Fin 2) (Fin 2) E) = (q : E) ^ (w + 1) * lam (Letter.D q)) → (∀ V : Submodule E (Fin 2 → E), (∀ s v, v ∈ V → (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) → ∃ (m : ℕ) (π : Fin m → (E ⊗[ℤ_[l]] X.Fn l) →ₗ[E] (Fin 2 → E)) (σ : Fin m → (Fin 2 → E) →ₗ[E] (E ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra E Letter), P ∈ admissibleLettersSubalgebra E N l ∧ FreeAlgebra.lift E lam P = 1 ∧ (∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∑ i, σ i (π i x) = x) ∧ (∀ i v, σ i v ∈ X.VB N l w E) ∧ (∀ i s, ∀ x ∈ X.VB N l w E, π i (X.galV l E s x) = (ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ π i x) ∧ (∀ i s v, X.galV l E s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) E) *ᵥ v)) ∧ (∀ i (T : Letter) v, admitted N l T → X.opV N l E T (σ i v) = lam T • σ i v) ∧ (∀ i (T : Letter), admitted N l T → ∀ x ∈ X.VB N l w E, π i (X.opV N l E T x) = lam T • π i x) ∧ (∀ i j v, π i (σ j v) = if i = j then v else 0) ∧ ∀ x ∈ X.VB N l w E, FreeAlgebra.lift E (X.opV N l E) P x = ∑ i, σ i (π i x) := by
  intro Ω _ _ _ ε X hε han k g N l _ hl2 hgN hN5 hNl hk hk3 α hα hα1 hα2 lamC hT hU hD E _ _ _ hnorm ι
    w lam ρ S0 htr hdet hfrob hirr
  have hlp : l.Prime := Fact.out
  have hlN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd hlp).1 hNl.symm
  have hpot : SSPotB N l (k - 2) lamC :=
    _root_.GlobalTheory.KZ.SSPotBr.ssPotB_at_newform k g N l hgN hN5 hlp hlN hk hk3 α hα hα1 hα2 lamC hT hU hD
  have hw : Odd w := by
    obtain ⟨j, rfl⟩ := hk
    refine ⟨j - 1, ?_⟩
    show 2 * j + 1 - 2 = 2 * (j - 1) + 1
    omega
  have hpot' : SSPotB N l w (fun T => ι (lam T)) := by
    have : (fun T => ι (lam T)) = lamC := by
      funext T; simp [lam]
    rw [this]; exact hpot
  have hbb : X.SSBB N l w E lam :=
    _root_.GlobalTheory.KZ.Comp.ssbb_of_ssPotB ε X hε han N l w hl2 hN5 hNl hw ι lam hpot'
  exact GlobalTheory.T.galois_representation_of_eigensystem ε X hε han N l w hl2 hN5 hNl hw hnorm lam hbb ρ S0 htr hdet hfrob hirr

end GlobalTheory.KZ.HeckeProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonvanishingTransferCharacterSumsPowerSeriesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_transfer_characterSums_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Gs L : PowerSeries (Qbar l)) (a a' κ : Qbar l) (v v' : ℕ → Qbar l) (c₀ m₀ c₁ n₀ : ℕ) (φ : DirichletCharacter (Qbar l) l) (e : ℕ), l ≠ 2 → 1 ≤ e → 2 ≤ m₀ → (∀ n, Gs.coeff n ∈ c.O) → (∀ n, L.coeff n ∈ c.O) → ‖a‖ = 1 → ‖a'‖ = 1 → κ ≠ 0 → (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) → (∀ m, ‖v' m‖ = 1 ∧ Cg m (v' (m + 1)) (v' m)) → 2 ≤ c₀ → ¬ l ∣ c₀ → (∀ m, m₀ ≤ m → ∃ z : Qbar l, IsPrimitiveRoot z (l ^ m) ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → Cg (m - c₁) ((1 - (c₀ : Qbar l) * ψ⁻¹ (c₀ : ZMod (l ^ m))) * (v' m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) (v m * a ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval Gs (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) → (∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0) → ∃ n₁ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) → ¬ Cg (n₁ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass Gs r ξ x) 0 := by
  first | (exact @GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (exact GlobalTheory.KZ.Cmp.nonvanishing_transfer) | (intros; apply GlobalTheory.KZ.Cmp.nonvanishing_transfer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedPresOfShCoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.Smooth

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_sub_sub {m : ℕ} {a b a' b' : Qbar l} (h : Cg m a a') (h' : Cg m b b') : Cg m (a - b) (a' - b') := by
  have e : a - b - (a' - b') = (a - a') + -(b - b') := by ring
  rw [Cg, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h (by rw [norm_neg]; exact h'))

theorem isUnit_natCast_padic {d : ℕ} (hd : Nat.Coprime d l) : IsUnit (d : ℤ_[l]) := by
  have hlp : l.Prime := Fact.out
  by_contra h
  have h1 : ‖((d : ℤ) : ℤ_[l])‖ < 1 := by
    rw [← PadicInt.mem_nonunits]; simpa using h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hd.symm (Int.natCast_dvd_natCast.mp h1)

theorem smoothed_pres [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (hL : ∀ r, Layer2 c A ν r (Z r)) (hc : ∀ r, Continuous fun s => Z r s 1)
    (hI : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)))
        ζ P o := by
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_pos hlp.pos i).ne'⟩
    inferInstance
  have hpos : 0 < l ^ m := pow_pos hlp.pos _
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hz := hL m
  set z := Z m with hzdef
  set uu := ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right m hd₀) with huu
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hlv⟩ := hA
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker
  have hH : ∀ s, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ cycMod ℚ Ω l m s = 1 := fun s => Iff.rfl
  have hfix : ∀ s, cycMod ℚ Ω l m s = 1 → s ζ = ζ := fun s hs =>
    GlobalTheory.Col.fix_of_cycMod le_rfl hs hζ.pow_eq_one

  have hu₀ := isUnit_natCast_padic (l := l) hd₀
  obtain ⟨ρ, hρ, hρc⟩ := GlobalTheory.CycInertia.exists_mem_Ine_toZModPow Ω l A hl hu₀.unit m
  rw [hu₀.unit_spec, map_natCast] at hρc
  have hρD : ρ ∈ Dec (F := ℚ) A := Ine_le_Dec A hρ
  have hρi : ρ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hρ
  have hρζ : ρ ζ = ζ ^ d₀ := by
    have hspec : ρ ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l ρ : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω ρ) ζ hζ.pow_eq_one
    rw [hspec, hρc, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]
  have hcρ : (cycMod ℚ Ω l m ρ⁻¹)⁻¹ = uu := by
    rw [map_inv, inv_inv]
    exact Units.ext (by rw [huu, ZMod.coe_unitOfCoprime]; exact hρc)
  have z11 : z 1 1 = 0 := GlobalTheory.KZ.UnitPres.layer_one hz
  have key : ∀ s ∈ H, z s uu = z (ρ⁻¹ * s * ρ) 1 := by
    intro s hs
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    have hsD := Ine_le_Dec A hsI
    have e1 := hz.2 ρ⁻¹ (inv_mem hρD) (s * ρ) (mul_mem hsD hρD) 1
    have e2 := hz.2 s hsD ρ hρD uu
    have e3 := hz.2 ρ⁻¹ (inv_mem hρD) ρ hρD 1
    rw [hcρ] at e1 e3
    rw [inv_mul_cancel, z11, hI _ hρi, Units.val_one, one_mul, one_mul] at e3
    rw [hI _ hρi, Units.val_one, one_mul, one_mul] at e1
    rw [hI _ hsI, Units.val_one, one_mul, hsc, inv_one, mul_one] at e2
    rw [mul_assoc]
    linear_combination -e1 - e2 + e3
  have hHρ : ∀ s ∈ H, ρ⁻¹ * s * ρ ∈ H := fun s hs => by
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    refine (hH _).2 ⟨?_, ?_⟩
    · have := conj_mem_Ine (inv_mem hρD) hsI
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hsc, mul_one, map_inv, inv_mul_cancel]
  obtain ⟨ι, hι, o, crd, ho, hadd, hzero, hcrd, -⟩ := GlobalTheory.CoefCoord.coord_mod_pow l c m
  obtain ⟨U, hU, hUz⟩ := GlobalTheory.KZ.UnitPres.exists_open (fun s => z s 1) (hc m) z11 m
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧
      ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (crd (z s 1) i) := fun i =>
    GlobalTheory.KumFix.exists_kumVal l Ω m H (GlobalTheory.isClosed_Ine_inf_ker_cycMod l Ω A _) ζ hζ
      (fun s hs => hfix s hs.2) (fun s => crd (z s 1) i)
      (fun s hs t ht => by
        show crd (z (s * t) 1) i = crd (z s 1) i + crd (z t 1) i
        rw [GlobalTheory.KZ.UnitPres.layer_add hz (Ine_le_Dec A hs.1) (Ine_le_Dec A ht.1) hs.2, hI s hs.1, Units.val_one, one_mul,
          hadd _ (hz.1 _ _) _ (hz.1 _ _), Pi.add_apply])
      U hU (fun s _ hs => by
        show crd (z s 1) i = 0
        rw [hzero _ (hz.1 _ _) (hUz s hs), Pi.zero_apply])
  choose u hu0 hufix huk using hex

  have hw0 : ∀ i, u i * (ρ (u i))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (hu0 i) (inv_ne_zero ((map_ne_zero ρ).2 (hu0 i)))
  have hvw : ∀ i, A.valuation (u i * (ρ (u i))⁻¹) = 1 := fun i => by
    rw [map_mul, map_inv₀, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hρD, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 (hu0 i)
  have hwfix : ∀ i, ∀ s ∈ H, s (u i * (ρ (u i))⁻¹) = u i * (ρ (u i))⁻¹ := fun i s hs => by
    have e : s (ρ (u i)) = ρ ((ρ⁻¹ * s * ρ) (u i)) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
    rw [map_mul, map_inv₀, hufix i s hs, e, hufix i _ (hHρ s hs)]
  have hP : ∀ i, ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧
      P.eval ζ = u i * (ρ (u i))⁻¹ := fun i =>
    GlobalTheory.CycIne.exists_poly_of_fixed l Ω A hA m ζ hζ _ ((A.valuation_le_one_iff _).1 (hvw i).le)
      (fun s h1 h2 => hwfix i s ((hH s).2 ⟨h1, h2⟩))
  choose P hPc hPe using hP
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'

  have hkw : ∀ s ∈ H, ∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i * (ρ (u i))⁻¹) s
      ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)) := by
    intro s hs i
    obtain ⟨v, hv, hsv⟩ := huk i s hs
    obtain ⟨v', hv', hsv'⟩ := huk i _ (hHρ s hs)
    refine GlobalTheory.KZ.UnitPres.kumVal_int hζ.pow_eq_one (v := v * (ρ v')⁻¹) ?_ ?_
    · rw [mul_pow, inv_pow, ← map_pow, hv', hv]
    · have e : s (ρ v') = ρ ((ρ⁻¹ * s * ρ) v') := by
        rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
      rw [map_mul, map_inv₀, hsv, e, hsv', map_mul, map_pow, hρζ, zpow_sub₀ hζ0, zpow_mul]
      simp only [zpow_natCast]
      ring
  refine ⟨ι, hι, P, o, hζ, hPc, fun i => (ho i).1, fun i => by rw [hPe]; exact hw0 i, ?_⟩
  show GlobalTheory.Col.KumPres A m m (ζ ^ l ^ 0) _ _ _
  rw [pow_zero, pow_one]
  refine ⟨hζ, le_rfl, fun i => ?_, fun i => (ho i).2, fun s hs hc' _ => ?_⟩
  · simp only [hPe]
    refine ⟨(A.valuation_le_one_iff _).1 (hvw i).le, hw0 i, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, hvw i, inv_one]
  · have hsH : s ∈ H := (hH s).2 ⟨hs, hc'⟩
    refine ⟨fun i => ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)),
      fun i => by simp only [hPe]; exact hkw s hsH i, ?_⟩
    show Cg m (z s 1 - (d₀ : Qbar l) * z s (1 * uu)) _
    rw [one_mul, key s hsH]
    have h2 := hcrd _ (hz.1 s 1)
    have h3 := hcrd _ (hz.1 (ρ⁻¹ * s * ρ) 1)
    have h4 := cg_sub_sub h2 (GlobalTheory.KumUnit.cg_mul_left (o := (d₀ : Qbar l)) (IsUltrametricDist.norm_natCast_le_one (Qbar l) d₀) h3)
    refine GlobalTheory.KumUnit.cg_trans h4 (GlobalTheory.KumUnit.cg_symm (GlobalTheory.KumUnit.cg_trans
      (GlobalTheory.KumUnit.cg_sum _ fun i _ => GlobalTheory.KumUnit.cg_mul_left (ho i).2 (GlobalTheory.KZ.UnitPres.cg_intCast _ _)) ?_))
    have e : (∑ i, o i * ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : Qbar l)) =
        (∑ i, o i * ((crd (z s 1) i).val : Qbar l)) - (d₀ : Qbar l) * ∑ i, o i * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : Qbar l) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e, Cg, sub_self, norm_zero]
    exact norm_nonneg _

theorem smoothed_pres_of_shCoc [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hD : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0)
    (hI : ∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hY : ∀ r, GlobalTheory.KA.ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r))
    (hc : ∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : G ℚ Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) →
      Cg n (Y r (s * s') y 1) (Y r s y 1))
    (hO : ∀ r s y, Y r s y 1 ∈ c.O) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Y r s y 1 - (d₀ : Qbar l) *
        Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  classical
  have hnz : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 := by
    intro s hs h
    have := (ρ s).det_ne_zero
    rw [Matrix.det_fin_two, hD s hs, h] at this
    simp at this
  let ν : G ℚ Ω → (Qbar l)ˣ := fun s =>
    if h : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 then Units.mk0 _ h else 1
  have hν : ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 := by
    intro s hs
    simp only [ν, dif_pos (hnz s hs), Units.val_mk0]
  refine smoothed_pres A hA c ν (fun r s y => Y r s y 1) (fun r => ⟨hO r, fun s hs u _ x => ?_⟩)
    (fun r => GlobalTheory.LambdaValuationPowers.AllRoots.continuous_of_cg _ fun n => ?_) (fun s hs => ?_) d₀ hd₀ m ζ hζ
  · have := congrFun (hY r s u x) 1
    show Y r (s * u) x 1 = Y r s x 1 + (ν s : Qbar l) * Y r u (x * (cycMod ℚ Ω l r s)⁻¹) 1
    rw [this, hν s hs]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD s hs]
  · obtain ⟨E0, hE⟩ := hc r n
    exact ⟨E0, fun s s' h => hE s s' 1 h⟩
  · exact Units.ext (by rw [hν s (Ine_le_Dec A hs), hI s hs, Units.val_one])

theorem exists_pres_smoothed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₀' : ℕ), ∀ m, m₀ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
    HTPresNuOfPolys A cf m c₀' (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  intro l _ Ω _ _ _ ι e S A W g hN hS ε X pr N _ cw c d gm ψ₀ cf α _ _ _ hAdm _ j _ c₀ Y hZ hY hc hO d₀ hd₀ _
  refine ⟨0, 0, fun m _ ζ hζ => ?_⟩
  by_cases hcw : ∃ x, cw x ≠ 0
  · obtain ⟨x, hx⟩ := hcw
    obtain ⟨ρ, hρ, -, hD, hI, -⟩ := GlobalTheory.RhoAdm.rho_ordinary_shape l Ω ι e S A W g ψ₀ hN hS
      (hAdm.1 x hx).2.2.2.2.2.2.2.2.2.2.2
    have hfun : rhoK W e ψ₀ = fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := funext fun s => (hρ s).symm
    exact smoothed_pres_of_shCoc A hN.atL cf ρ hD hI Y (fun r => hfun ▸ hY r) hc hO d₀ hd₀ m ζ hζ
  · refine GlobalTheory.LambdaValuationPowers.AllRoots.pres_of_vanish A cf _ m ζ hζ fun s _ _ => ?_
    obtain ⟨Yx, -, hs⟩ := hZ
    push_neg at hcw
    simp [hs, hcw]

end GlobalTheory.LambdaValuationPowers.Smooth
end
end

