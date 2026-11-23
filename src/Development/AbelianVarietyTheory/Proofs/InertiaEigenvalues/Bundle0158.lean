module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
section
open ReciprocityTheory.Gal

open Polynomial IntermediateField

namespace GlobalTheory.ShapeNeg

theorem natDegree_minpoly_le_mul {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) (hx : IsIntegral K x) :
    (minpoly ℚ_[p] x).natDegree ≤ (minpoly K x).natDegree * Module.finrank ℚ_[p] K := by
  set E := K⟮x⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hx
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  have h1 : Module.finrank ℚ_[p] K * Module.finrank K E = Module.finrank ℚ_[p] E :=
    Module.finrank_mul_finrank ℚ_[p] K E
  rw [adjoin.finrank hx] at h1
  have hxE : x ∈ E := mem_adjoin_simple_self K x
  haveI : IsScalarTower ℚ_[p] E (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h2 : minpoly ℚ_[p] (⟨x, hxE⟩ : E) = minpoly ℚ_[p] x :=
    (minpoly.algebraMap_eq (algebraMap E (PadicAlgCl p)).injective (⟨x, hxE⟩ : E)).symm
  have h3 := minpoly.natDegree_le (A := ℚ_[p]) (⟨x, hxE⟩ : E)
  rw [h2] at h3
  rw [mul_comm]
  omega

theorem natDegree_minpoly_le_card_pow_eq_one {p : ℕ} [Fact p.Prime]
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {N : ℕ} [NeZero N] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ) :
    (minpoly K ζ).natDegree ≤ Nat.card {x : ZMod N // x ^ k = 1} := by
  classical
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hirr : Irreducible (minpoly K ζ) := minpoly.irreducible hint
  have hsep : (minpoly K ζ).Separable := hirr.separable
  have hspl : Splits ((minpoly K ζ).map (algebraMap K (PadicAlgCl p))) := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl, ← Nat.card_eq_fintype_card]
  have hχ : ∀ σ : Formalism.GaloisCohomology.GK p K, ((hζ.autToPow K σ : ZMod N)) ^ k = 1 := by
    intro σ
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 := hζ.autToPow_spec K (σ ^ k)
    rw [hfix σ] at h1
    have h0 : ζ ^ (1 % N) = ζ := by rw [hζ.eq_orderOf, pow_mod_orderOf, pow_one]
    have h2 : ζ ^ (hζ.autToPow K (σ ^ k) : ZMod N).val = ζ ^ (1 % N) := h1.trans h0.symm
    have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
    rw [← ZMod.val_one_eq_one_mod] at h3
    exact ZMod.val_injective N h3
  have horb : ∀ y : (minpoly K ζ).rootSet (PadicAlgCl p), ∃ σ : Formalism.GaloisCohomology.GK p K, σ ζ = y := by
    intro y
    have hy : aeval (y : PadicAlgCl p) (minpoly K ζ) = 0 :=
      (mem_rootSet.1 y.2).2
    have he : minpoly K ζ = minpoly K (y : PadicAlgCl p) :=
      minpoly.eq_of_irreducible_of_monic hirr hy (minpoly.monic hint)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (PadicAlgCl p)).1 he.symm
    exact ⟨σ, hσ⟩
  choose σ hσ using horb
  refine Nat.card_le_card_of_injective (fun y => ⟨(hζ.autToPow K (σ y) : ZMod N), hχ (σ y)⟩) ?_
  intro y y' hyy
  have h : (hζ.autToPow K (σ y) : ZMod N) = (hζ.autToPow K (σ y') : ZMod N) :=
    congrArg Subtype.val hyy
  have h' : (σ y) ζ = (σ y') ζ := by
    rw [← hζ.autToPow_spec K (σ y), ← hζ.autToPow_spec K (σ y'), h]
  exact Subtype.ext (by rw [← hσ y, ← hσ y']; exact h')

theorem exists_pow_ne_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  intro p _ K hK k hk
  by_contra hcon
  push_neg at hcon
  have hp : p.Prime := Fact.out
  set d := Module.finrank ℚ_[p] K with hd
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * d < p ^ n := ⟨2 * k * d, Nat.lt_pow_self hp.one_lt⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  have hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ := fun σ => hcon σ (n + 1) ζ hζ.pow_eq_one
  have hB := natDegree_minpoly_le_card_pow_eq_one hζ k hfix
  have hC : Nat.card {x : ZMod (p ^ (n + 1)) // x ^ k = 1} ≤ 2 * k := by
    by_cases h2 : p = 2
    · subst h2
      exact GlobalTheory.card_pow_eq_one_two_pow_le (n + 1) (by omega) hk
    · haveI : IsCyclic (ZMod (p ^ (n + 1)))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 (n + 1)
      have := GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (p ^ (n + 1)) hk
      omega
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  have hA := natDegree_minpoly_le_mul hK ζ hint
  have hcyc : cyclotomic (p ^ (n + 1)) ℚ_[p] = minpoly ℚ_[p] ζ := by
    refine minpoly.eq_of_irreducible_of_monic (GlobalTheory.Cyc.Model.cyc_irred n) ?_ (cyclotomic.monic _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos _)
  rw [← hcyc, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hA
  rw [← hd] at hA
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h1 : p ^ n ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ hp1
  have h2 : (minpoly K ζ).natDegree * d ≤ 2 * k * d := Nat.mul_le_mul_right _ (hB.trans hC)
  omega

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem sl2Map_wS {F K : Type} [Field F] [CommRing K] [Algebra F K] :
    SpecialLinearGroup.map (algebraMap F K) (wS F) = wS K := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem weilSL2_hermitian : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  intro hW hG F E _ _ _ _ _ r M ψ hψ
  obtain ⟨A, e, j, hj, hNe⟩ := _root_.GlobalTheory.JR.exists_split_et F E r
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  haveI : CharZero F := Unram.charZero (E := E)
  letI mE : MeasurableSpace E := M.mE
  haveI : BorelSpace E := M.bE
  obtain ⟨hjc, hjsc⟩ := _root_.GlobalTheory.JR.et_equiv_continuous F E A r j
  let jh : A.L ≃ₜ (Fin r → E) := { j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }
  let μE : Measure (Fin r → E) := Measure.pi fun _ => M.μE
  let B : (Fin r → E) → (Fin r → E) → ℂ := fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))
  have hsd : SelfDual μE B := _root_.GlobalTheory.JR.selfDual_pi_trace F E r M ψ hψ
  obtain ⟨hT1, hT2⟩ := GlobalTheory.transport_selfDual_fourB j.toAddEquiv hjc hjsc μE B
  have hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y) := by
    funext x y
    have h1 := hj x y
    simp only [map_one, one_mul] at h1
    show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))
    rw [Units.val_one, one_mul, _root_.GlobalTheory.trace_tower_et, h1]
  have hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K)) := by
    rw [hker]; exact (hT1 ⟨hsd, fun x => (continuous_const.add continuous_id).aemeasurable⟩).1
  obtain ⟨γ, Wk, hWk⟩ := hW F E A ψ hψ 1 _ hsdL
  have hγ : γ = 1 := hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)
  obtain ⟨hTrE, -, -⟩ := _root_.GlobalTheory.NTr.traceForm_perfect F E
  have htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a := by
    intro a
    apply (algebraMap F E).injective
    rw [hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]; ring
  have hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2 := by
    intro y
    have : star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]
    rw [this, htr2, _root_.GlobalTheory.trace_eq_sum_coords_of_algEquiv r e]; field_simp
  have testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩
  have testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩
  have hz : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have hW0 : ∀ G, Wk G 0 = 0 := by
    intro G
    have := hWk.1.2.2.2 G 1 0 0 hz hz
    simp only [one_smul, add_zero] at this
    simpa using this
  let ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K := SpecialLinearGroup.map (algebraMap F A.K)
  let T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ :=
    fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)
  have hTt : ∀ g φ, IsTest φ → IsTest (T g φ) := fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))
  have hT0 : ∀ g, T g 0 = 0 := by
    intro g; funext b
    show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0
    have : (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0 := rfl
    rw [this, hW0]; rfl
  have hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2)) :=
    fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)
  refine ⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf; funext X
    show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X
    rw [map_one, hWk.1.2.1 _ (hsl f hf X)]
    simp
  · intro g h f hf; funext X
    show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)
    simp only [LinearEquiv.symm_apply_apply]
    rw [map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]
  · intro g c f f' hf hf'; funext X
    show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)
    have key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2)) := rfl
    rw [key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]
    rfl
  · intro f hf
    refine ⟨fun t X => ?_, ?_⟩
    · have hι : ι (nS t) = nS (algebraMap F A.K t) := by
        exact sl2Map_nS t
      show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _
      rw [hι, (hWk.2 _ (hsl f hf X)).1]
      have hy := hnorm (j.symm X.2.1)
      rw [LinearEquiv.apply_symm_apply] at hy
      simp only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]
    · have hι : ι (wS F) = wS A.K := by
        exact sl2Map_wS
      funext X
      show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X
      rw [hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]
      have e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1 := j.apply_symm_apply _
      rw [e1]
      show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
      simp only [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem weilHyp_rg : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ Φ : A.K × A.K → ℂ, Hyp.rg A 1 Φ = Φ) ∧ ∀ (g h : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), Hyp.rg A g (Hyp.rg A h Φ) = Hyp.rg A (g * h) Φ := by
  intro F E _ _ _ _ _ A
  refine ⟨fun Φ => ?_, fun g h Φ => ?_⟩
  · funext p
    simp [Hyp.rg]
  · funext p
    have hm : ((g * h : Matrix.SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) =
        (g : Matrix (Fin 2) (Fin 2) A.K) * (h : Matrix (Fin 2) (Fin 2) A.K) := Matrix.SpecialLinearGroup.coe_mul g h
    unfold Hyp.rg
    rw [hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    congr 1
    ext <;> ring

theorem weilHyp_nS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x z : A.K) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => A.psiK ψ (z * x * (p.1 * p.2)) * Φ p) = Hyp.rg A (nS z) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν ψ x z Φ
  funext p
  simp only [Hyp.pt, Hyp.rg, nS, fourB, Hyp.kx, Et.psiK]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add]
  congr 1
  funext b
  rw [show x * b * (p.1 * z + p.2) = z * x * (p.1 * b) + x * b * p.2 by ring, map_add (f := _), AddChar.map_add_eq_mul]
  ring

theorem weil_hyperbolic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  intro F E _ _ _ _ _ A ψ hψ hK hL x μ hμ
  obtain ⟨e, he, hse⟩ := _root_.GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField F E A hK hL
  obtain ⟨hci, hcc, hN, hker, hsm, hunit⟩ := _root_.GlobalTheory.JR.Hyp.coord_structure F E A e he hse
  obtain ⟨ν, hν⟩ := _root_.GlobalTheory.JR.Hyp.selfDual_kx_exists F E A ψ hψ x
  have hνH : ν.IsAddHaarMeasure := hν.1
  have hT := _root_.GlobalTheory.JR.Hyp.pt_isTest F E A ψ hψ x ν hνH
  have hDD := _root_.GlobalTheory.JR.Hyp.pt_pt_eq_reflect F E A ψ (x : A.K) ν hν
  obtain ⟨hTcc, hTci⟩ := _root_.GlobalTheory.JR.Hyp.isTest_coord F E A e hci hcc
  obtain ⟨hTrg, hTneg, hTsc, hTmul, hTlin⟩ := _root_.GlobalTheory.JR.Hyp.isTest_ops F E A
  obtain ⟨hpsi, hkerlc⟩ := GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ
  obtain ⟨hrg1, hrgm⟩ := weilHyp_rg F E A
  have hlin := _root_.GlobalTheory.JR.Hyp.pt_linear F E A ψ hψ (x : A.K) ν hνH
  set P := Hyp.pt A ν ψ (x : A.K) with hP
  have h4 : ∀ Φ, IsTest Φ → P (P (P (P Φ))) = Φ := by
    intro Φ hΦ
    rw [hDD Φ hΦ, hDD _ (hTneg Φ hΦ)]
    funext p
    simp
  have hW : ∀ g φ, Hyp.wHyp A e ν ψ x g φ = fun y => P (P (P (Hyp.rg A g (P (fun p => φ (Hyp.cc A e p)))))) (Hyp.ci A e y) :=
    fun _ _ => rfl

  have hkey : ∀ g φ (Φ' : A.K × A.K → ℂ), IsTest Φ' → Hyp.rg A g (P (fun p => φ (Hyp.cc A e p))) = P Φ' →
      Hyp.wHyp A e ν ψ x g φ = fun y => Φ' (Hyp.ci A e y) := by
    intro g φ Φ' hΦ' h
    rw [hW, h, h4 Φ' hΦ']
  have hetaK : ∀ s : A.Kˣ, A.etaK s = 1 := by
    intro s
    have h1 := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.2.1 (Hyp.cc A e ((s : A.K), 1)) (hunit s)
    rwa [hN, mul_one] at h1
  refine ⟨Hyp.wHyp A e ν ψ x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g φ hφ
    rw [hW]
    exact hTci _ (hT _ (hT _ (hT _ (hTrg g _ (hT _ (hTcc φ hφ))))))
  · intro φ hφ
    rw [hW, hrg1, h4 _ (hTcc φ hφ)]
    funext y
    show φ (Hyp.cc A e (Hyp.ci A e y)) = φ y
    rw [hcc]
  · intro g h φ hφ
    have hin : (fun p => Hyp.wHyp A e ν ψ x h φ (Hyp.cc A e p)) = P (P (P (Hyp.rg A h (P (fun p => φ (Hyp.cc A e p)))))) := by
      funext p
      rw [hW]
      simp only [hci]
    rw [hW (g * h) φ, hW g (Hyp.wHyp A e ν ψ x h φ), hin, h4 _ (hTrg h _ (hT _ (hTcc φ hφ))), hrgm]
  · intro g c φ φ' hφ hφ'
    have hc1 : (fun p => (c • φ + φ') (Hyp.cc A e p)) = c • (fun p => φ (Hyp.cc A e p)) + (fun p => φ' (Hyp.cc A e p)) := rfl
    have t1 := hTcc φ hφ
    have t2 := hTcc φ' hφ'
    have hrl : ∀ (Φ Φ' : A.K × A.K → ℂ), Hyp.rg A g (c • Φ + Φ') = c • Hyp.rg A g Φ + Hyp.rg A g Φ' := fun _ _ => rfl
    rw [hW, hW, hW, hc1, hlin c _ _ t1 t2, hrl, hlin c _ _ (hTrg g _ (hT _ t1)) (hTrg g _ (hT _ t2)),
      hlin c _ _ (hT _ (hTrg g _ (hT _ t1))) (hT _ (hTrg g _ (hT _ t2))),
      hlin c _ _ (hT _ (hT _ (hTrg g _ (hT _ t1)))) (hT _ (hT _ (hTrg g _ (hT _ t2))))]
    rfl
  · intro φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro z y
      have hΦ : IsTest (fun p : A.K × A.K => A.psiK ψ (z * (x : A.K) * (p.1 * p.2)) * φ (Hyp.cc A e p)) :=
        hTmul _ _ (hpsi.comp_continuous (by fun_prop)) (hTcc φ hφ)
      rw [hkey (nS z) φ _ hΦ (weilHyp_nS F E A ν ψ (x : A.K) z _).symm]
      simp only
      rw [← hN, hcc]
    · intro s y
      have hΦ : IsTest (fun p : A.K × A.K => (A.absK (s : A.K) : ℂ) * φ (Hyp.cc A e ((s : A.K) * p.1, (s : A.K) * p.2))) :=
        hTmul _ _ (IsLocallyConstant.const _) (hTsc s _ (hTcc φ hφ))
      rw [hkey (mS s) φ _ hΦ (_root_.GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS F E A ν hνH ψ (x : A.K) s (fun p => φ (Hyp.cc A e p))).symm]
      simp only
      rw [hetaK, one_mul, ← hsm, hcc]
    · intro y
      rw [one_mul]
      exact _root_.GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB F E A ψ (x : A.K) e ν μ hT hDD (fun Φ hΦ => hTrg _ Φ hΦ) hTcc hcc (hker ψ (x : A.K))
        (hkerlc (x : A.K)) (_root_.GlobalTheory.JR.Hyp.measure_eq_coords F E A ψ hψ x e he hse ν μ hν hμ) φ hφ y

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FilteredIsoOfFilZero
section
noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]

variable [TopologicalSpace G] [TopologicalSpace LL]

section Whole

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  {ρ : Representation LL G V} {ρ' : Representation LL G V'}

omit [TopologicalSpace G] [TopologicalSpace LL]

end Whole

end Generic

section At

variable (K LL : FinExt l)

end At

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_mapdR_eq {K LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {T T' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.mapdR P f = _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mapdR (Qp := ℚ_[l]) (BdR := P.R.BdR) f :=
  rfl

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem strictness_of_dualExactSequence_strict
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore
  · intro K s LL hg T₀ T₁ T₂ f g hf hg' hi he hs h₀ h₁ h₂ τ a
    obtain ⟨k₁, k₂, k₃⟩ := h K s LL hg T₀ T₁ T₂ f g ⟨hf, hg', hi, he, hs⟩ h₀ h₁ h₂ τ a
    simp only [dualExactSequence_mapdR_eq] at k₁ k₂ k₃
    refine ⟨k₁, ?_, ?_⟩
    · ext y
      simpa [Submodule.mem_inf] using k₂ y
    · ext z
      simpa using k₃ z

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_strict_of_strictness
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb
  · intro K s LL hg T₀ T₁ T₂ f g hfg h₀ h₁ h₂ τ a
    obtain ⟨hf, hg', hi, he, hs⟩ := hfg
    have k := h K s LL hg T₀ T₁ T₂ f g
    have k' := k hf hg' hi he hs
    have k'' := k' h₀ h₁ h₂
    have k3 := k'' τ
    have k4 := k3 a
    obtain ⟨k₁, k₂, k₃⟩ := k4
    refine ⟨k₁, fun y => ?_, fun z => ?_⟩
    · have := SetLike.ext_iff.mp k₂ y
      simpa [Submodule.mem_inf, dualExactSequence_mapdR_eq] using this
    · have := SetLike.ext_iff.mp k₃ z
      simpa [dualExactSequence_mapdR_eq] using this

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
theorem _root_.GlobalTheory.DeRhamCompare.strict_iff :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  ⟨strictness_of_dualExactSequence_strict P,
    dualExactSequence_strict_of_strictness P⟩

end GlobalTheory.DeRhamCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem ko_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨a * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul]
  congr 1
  rw [hu]
  calc a * ((u⁻¹ : Oˣ) : O) * ((u : O) * ϖ ^ n) = a * ϖ ^ n * (((u⁻¹ : Oˣ) : O) * u) := by ring
    _ = ϖ ^ n * a := by simp [mul_comm]

end GlobalTheory.ShapeNeg
end

