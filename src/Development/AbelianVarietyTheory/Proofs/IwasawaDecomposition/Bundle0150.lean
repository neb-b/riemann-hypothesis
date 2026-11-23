module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormValuesNearPointSpec
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke.ValAt

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem atV_mul {v : HeightOneSpectrum (𝓞 F)} {η η' : GA σ J} (h : AtV v η) (h' : AtV v η') : AtV v (η * η') := by
  intro v' hv'
  rw [Subgroup.coe_mul, map_mul, h v' hv', h' v' hv', one_mul]

theorem atV_inv {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) : AtV v η⁻¹ := by
  intro v' hv'
  rw [Subgroup.coe_inv, map_inv, h v' hv', inv_one]

theorem inv_loc {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hb : v ∉ bad) (g) (hg : g ∈ AdFun S emb) (x κ : GA σ J) (hκ : AtV v κ)
    (hU : bc (prV (E := E) v) κ.1 ∈ S.Uloc v) : g (x * κ) = g x := by
  have hm : κ.1 ∈ S.U := by
    refine (S.U_eq _).2 ⟨κ.2, fun v' => ?_⟩
    by_cases h : v' = v
    · subst h; exact hU
    · rw [hκ v' h]; exact Subgroup.one_mem _
  have hc : S.chi ⟨κ.1, hm⟩ = 1 := S.chi_triv _ (fun v' hv' => hκ v' (fun h => hb (h ▸ hv')))
  funext y
  have := hg 1 (Subgroup.one_mem _) x (x * κ) ⟨κ.1, hm⟩ (by rw [map_one, one_mul]; rfl) y y
    (fun τ => by simp [atInf])
  rw [this, hc, Units.val_one, one_mul]

theorem val_self {ι : Type} [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : Type} [Field k]
    (p : GA σ J → Pr (𝓞 E) (Fin n → E) k) (hb : v ∉ bad) (hp : PMap S v hv p) (g) (hg : g ∈ AdFun S emb)
    (x η : GA σ J) (hη : AtV v η) : valAt v p g x (p (x * η)) = g (x * η) := by
  have h : ∃ η', AtV v η' ∧ p (x * η') = p (x * η) := ⟨η, hη, rfl⟩
  unfold valAt
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = η0 at h1 h2
  have e : x * η = x * η0 * (η0⁻¹ * η) := by group
  rw [e]
  refine (inv_loc S emb v hb g hg _ _ (atV_mul (atV_inv h1) hη) ?_).symm
  exact (hp.2.1 (x * η0) _).1 (by rw [← e, h2])

end

theorem valAt_spec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ g ∈ AdFun S emb, (∀ x η : GA σ J, AtV v η → valAt v p g x (p (x * η)) = g (x * η)) ∧ (∀ x η : GA σ J, AtV v η → valAt v p g (x * η) = valAt v p g x) ∧ ∀ (a : ℤ) (δ x : GA σ J) (q : Pr (𝓞 E) (Fin n → E) k), (a : k) ≠ 0 → IsDia S v hv a δ → valAt v p g x (q.dil (a : k)) = valAt v p (fun y => g (y * δ)) x q := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp g hg
  have key := val_self S emb v hv p hb hp g hg
  refine ⟨key, fun x η hη => ?_, fun a δ x q ha hδ => ?_⟩
  · funext q
    by_cases h : ∃ η', AtV v η' ∧ p (x * η * η') = q
    · obtain ⟨η', h1, rfl⟩ := h
      rw [key _ _ h1, mul_assoc, key _ _ (atV_mul hη h1)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η⁻¹ * η', atV_mul (atV_inv hη) h1, ?_⟩
        rw [← h2]; congr 1; group
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']
  · have hδv : AtV v δ := hδ.1
    by_cases h : ∃ η', AtV v η' ∧ p (x * η') = q
    · have hR : valAt v p (fun y => g (y * δ)) x q = g (x * h.choose * δ) := by
        unfold valAt
        rw [dite_eq_left h]
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [hR]
      generalize h.choose = η0 at h1 h2
      rw [← h2, ← hp.2.2 _ δ a hδ, mul_assoc, key _ _ (atV_mul h1 hδv)]
    · have h' : ¬ ∃ η', AtV v η' ∧ p (x * η') = q.dil (a : k) := by
        rintro ⟨η', h1, h2⟩
        refine h ⟨η' * δ⁻¹, atV_mul h1 (atV_inv hδv), ?_⟩
        have h3 := hp.2.2 (x * (η' * δ⁻¹)) δ a hδ
        have e : x * (η' * δ⁻¹) * δ = x * η' := by group
        rw [e, h2] at h3
        have h4 := congrArg (Pr.dil (a : k)⁻¹) h3
        rw [Pr.dil_dil, Pr.dil_dil, inv_mul_cancel₀ ha, Pr.dil_one, Pr.dil_one] at h4
        exact h4.symm
      unfold valAt
      rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.LevelHecke.ValAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEq
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeWittLoc

open Matrix Formalism.UG

theorem exists_quasiReflection {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin n → S) (c : S)
    (hc : c + s c = c * s c * hform s J w w) :
    ∃ g g' : Matrix (Fin n) (Fin n) S, g' * g = 1 ∧ cT s g * J = J * g' ∧
      ∀ z, g *ᵥ z = z - (c * hform s J w z) • w := by
  let r : Fin n → S := fun j => ∑ i, s (w i) * J i j
  have hr : ∀ z, r ⬝ᵥ z = hform s J w z := fun z => by
    simp only [r, dotProduct, hform, Finset.sum_mul]
    exact Finset.sum_comm
  let P : Matrix (Fin n) (Fin n) S := vecMulVec w r
  have hPP : P * P = hform s J w w • P := by
    ext i j
    rw [← hr]
    simp only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : cT s P * J = J * P := by
    ext i j
    have h1 : s (r i) = ∑ k, J i k * w k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [r, map_sum, map_mul, hs, hJ]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]
    calc ∑ k, s (w k) * s (r i) * J k j = s (r i) * r j := by
          simp only [r, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          rw [h1, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul,
      mul_comm (s c) c, ← hc, add_smul]
    abel
  · have : cT s (1 - c • P) = 1 - s c • cT s P := by
      ext i j
      simp [cT, Matrix.one_apply, eq_comm]
    rw [this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul,
      Matrix.mul_one]
  · rw [sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]
    congr 1
    ext i
    simp only [P, Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_unitary {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → S) (β v : S)
    (hx : hform s J x x = β) (hy : hform s J y y = β) (hv : v * s v = 1)
    (hD : IsUnit (β - v * hform s J y x)) :
    ∃ γ : GL (Fin n) S, cT s γ.1 * J * γ.1 = J ∧ γ.1 *ᵥ x = y := by
  have hsym : ∀ a b, s (hform s J a b) = hform s J b a := fun a b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hform, map_sum, map_mul, hs, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hD.exists_left_inv
  have hβ : s β = β := by rw [← hx, hsym]
  have hc' : s c * (β - s v * hform s J x y) = 1 := by
    have := congrArg s hc
    rwa [map_mul, map_sub, map_mul, hsym, hβ, map_one] at this
  obtain ⟨g, g', h1, h2, h3⟩ := exists_quasiReflection s hs J hJ (x - s v • y) c (by
    rw [hl, hrr, hrr, hx, hy]
    linear_combination (-c) * hc' - s c * hc - c * s c * β * hv)
  have h4 : g * g' = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hv, h4, one_smul]
  · rw [smul_mul_smul_comm, mul_comm, hv, h1, one_smul]
  · have : cT s (v • g) = s v • cT s g := by
      ext i j
      simp [cT]
    show cT s (v • g) * J * (v • g) = J
    rw [this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul,
      Matrix.mul_one]
  · show (v • g) *ᵥ x = y
    rw [smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]

theorem exists_isUnit_sub {S : Type} [CommRing S] [Finite (MaximalSpectrum S)] (v : ℕ → S)
    (hv : ∀ k l, k ≠ l → IsUnit (v k - v l)) (β t : S) (hβ : IsUnit β) :
    ∃ k, IsUnit (β - v k * t) := by
  by_contra h
  push Not at h
  choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)
  obtain ⟨k, l, hkl, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))
  have he' : m k = m l := congrArg MaximalSpectrum.asIdeal he
  have h1 := hmem l
  rw [← he'] at h1
  have h2 : (v k - v l) * t ∈ m k := by
    have := (m k).sub_mem h1 (hmem k)
    convert this using 1
    ring
  have h3 : t ∈ m k := ((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2
  have h4 : β ∈ m k := by
    have := (m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)
    rwa [sub_add_cancel] at this
  exact (hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)

theorem exists_normOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k, a k * σ (a k) = 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | (apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)

theorem exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy
  have := hR'.1
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  obtain ⟨a, ha, hn⟩ := exists_normOne hcm
  obtain ⟨k, hk⟩ := exists_isUnit_sub (fun k => inclR R (a k))
    (fun k l hkl => by
      rw [← map_sub]
      exact (IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)
    (algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)
  obtain ⟨γ, h1, h2⟩ := exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J)
    (fun i j => by
      show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
      rw [hJ.1])
    (x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))
    (by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by
      show inclR R (a k) * inclR R (σ (a k)) = 1
      rw [← map_mul, hn, map_one])
    hk
  refine ⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h2

end GlobalTheory.GaugeWittLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffPowEqZeroOfDegreeLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscExpDeriv

theorem coeff_pow_eq_zero_of_degree_lt {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (n : ℕ) :
    ∀ γ : σ →₀ ℕ, γ.degree < n → AddMonoidAlgebra.coeff (q ^ n) γ = 0 := by
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ h
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h2 : x.2 = 0
    · rw [h2, hq, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have hs : x.1.degree + x.2.degree = γ.degree := by rw [← hx', map_add (f := _)]
      rw [ih x.1 (by omega), zero_mul]

theorem coeff_expPS_eq_sum {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (γ : σ →₀ ℕ) (N : ℕ) (hN : γ.degree < N) :
    MvPowerSeries.coeff γ (expPS q) =
      ∑ n ∈ Finset.range N, AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) := by
  change ∑ n ∈ Finset.range (γ.degree + 1), AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) = _
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_degree_lt q hq n γ (by simp only [Finset.mem_range] at hn; omega),
    zero_div]

theorem coeff_deriv_expPS : ∀ (σ : Type) [DecidableEq σ] (q : MvPolynomial σ ℂ),
    AddMonoidAlgebra.coeff q 0 = 0 → ∀ (l : σ) (α : σ →₀ ℕ),
      ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS q) =
        MvPowerSeries.coeff α
          (((MvPolynomial.pderiv l q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * expPS q) := by
  intro σ _ q hq l α
  rw [coeff_expPS_eq_sum q hq _ (α.degree + 1 + 1)
    (by rw [map_add (f := _), Finsupp.degree_single]; omega), Finset.mul_sum, MvPowerSeries.coeff_mul]
  have h1 : ∀ n : ℕ, ((α l : ℂ) + 1) *
      (AddMonoidAlgebra.coeff (q ^ n) (α + Finsupp.single l 1) / (n.factorial : ℂ)) =
      AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ n)) α / (n.factorial : ℂ) := by
    intro n
    rw [MvPolynomial.coeff_pderiv]
    ring
  simp only [h1]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_div, add_zero]
  have h2 : ∀ n : ℕ, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ (n + 1))) α /
      (((n + 1).factorial : ℕ) : ℂ) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l q) x.1 *
        (AddMonoidAlgebra.coeff (q ^ n) x.2 / (n.factorial : ℂ)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, mul_comm, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_mul, Nat.factorial_succ, nsmul_eq_mul]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hs : x.1.degree + x.2.degree = α.degree := by rw [← hx', map_add (f := _)]
  rw [coeff_expPS_eq_sum q hq x.2 (α.degree + 1) (by omega), MvPolynomial.coeff_coe, Finset.mul_sum]

end GlobalTheory.OscExpDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem continuous_matrix_inv_of_isUnit_det {T n : Type} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {M : T → Matrix n n ℂ} (hM : Continuous M) (h : ∀ t, IsUnit (M t).det) : Continuous fun t => (M t)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun t => (h t).ne_zero).smul hM.matrix_adjugate

theorem continuous_ker_right (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ)
    (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ) (hY : Continuous Y')
    (hv : Continuous v') (hφ : Continuous φ') (h : ∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) :
    Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  have hM : Continuous fun t => Yᴴ * Jm P Q * Y' t := continuous_const.matrix_mul hY
  have hI := continuous_matrix_inv_of_isUnit_det hM h
  unfold ker
  refine (hM.neg.matrix_det.inv₀ fun t => ?_).mul (Complex.continuous_exp.comp (Continuous.sub
    (continuous_const.dotProduct hv) ((continuous_const.add hφ).dotProduct
      ((((hY.matrix_mul hI).matrix_mul continuous_const).matrix_mul continuous_const).matrix_mulVec
        (continuous_const.add hv)))))
  rw [Pi.neg_apply, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h t).ne_zero

end GlobalTheory.OscGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField
open scoped TensorProduct

namespace GlobalTheory.RationalCountable

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem discrete_countable_GQ :
    ∀ (D : D7) (V : HSp D), DiscreteTopology (GQ V) ∧ Countable (GQ V) :=
  fun D V => ⟨GlobalTheory.RationalDiscrete.discreteTopology_GQ D V,
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram⟩

end GlobalTheory.RationalCountable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroupsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_reps_conjugate_level_groups : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | exact GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | (intros; apply GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effCartier_of_proportional_sections : ∀ (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W), GeneratesAlong I σ g → Proportional σ g ψ → IsSchemeTheoreticallyDominant d → QuasiCompact d → (∀ t : T, d t ∉ I.support) → FinalTheorems.EffCartier I := by
  first | exact @GlobalTheory.ProjBlowup.effCartier_of_proportional | exact GlobalTheory.ProjBlowup.effCartier_of_proportional | (intros; apply GlobalTheory.ProjBlowup.effCartier_of_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegralOrthogonalComplementPair
section
noncomputable section

namespace GlobalTheory.GaugeEx.PairLat

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem ev_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (Fv F v) e ∈ intV b v := by
  filter_upwards [IntBasis.ev_int_coord b e] with v hv
  exact IntBasis.tmul_mem b v (one_mem _) hv

theorem ev_map {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, A.map (inclR (Fv F v)) i j ∈ intV b v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_incl b (A i j)

theorem mulVec_mem (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y ∈ intV b v, ∀ z ∈ intV b v, y * z ∈ intV b v) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intV b v)
    (w : Fin n → Fv F v ⊗[F] E) (hw : ∀ j, w j ∈ intV b v) (i : Fin m) :
    A.mulVec w i ∈ intV b v := by
  have h : A.mulVec w i = ∑ j, A i j * w j := rfl
  rw [h]
  exact IntBasis.sum_mem' b v Finset.univ (fun j => A i j * w j) fun j _ => hm _ (hA i j) _ (hw j)

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : HA (Fv F v) σ J, (∀ i j, (HA.mat (Fv F v) σ J k).val i j ∈ intV b v ∧ (HA.mat (Fv F v) σ J (k)⁻¹).val i j ∈ intV b v) → ∀ (y : Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) (y' : Fin 1 → Fin M → Fv F v ⊗[F] E), pairOf (Fv F v) σ J B y k y' ∈ latV b v ↔ y ∈ latV b v ∧ y' ∈ latV b v := by
  intro F E _ _ _ _ _ σ d b M J x a B J' hS
  obtain ⟨-, -, -, -, hJ', hH⟩ := hS
  have hdet : J'.det ≠ 0 := hH.2
  set C : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J) with hC
  have hCB : C * B = 1 := by
    rw [hC, Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  filter_upwards [(IntBasis.main F E σ d b).2.1, ev_map b B, ev_map b C] with v hv hB hCv k hk y y'
  have hm := hv.2.1
  simp only [mem_latV_iff, Fin.forall_fin_two, Fin.forall_fin_one]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := mulVec_mem b v hm _ hCv _ (mulVec_mem b v hm _ (fun i j => (hk i j).2) _ h)
    have h2 : (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        (pairOf (Fv F v) σ J B y k y' 1)) = y' 0 := by
      change (C.map (inclR (Fv F v))).mulVec (((HA.mat (Fv F v) σ J k)⁻¹).val.mulVec
        ((HA.mat (Fv F v) σ J k).val.mulVec ((B.map (inclR (Fv F v))).mulVec (y' 0)))) = y' 0
      rw [Matrix.mulVec_mulVec _ _ (HA.mat (Fv F v) σ J k).val, Units.inv_mul, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    intro i
    rw [← h2]
    exact h1 i
  · exact mulVec_mem b v hm _ (fun i j => (hk i j).1) _ (mulVec_mem b v hm _ hB _ h)

end GlobalTheory.GaugeEx.PairLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proj_map_proportional_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R), GeneratesAlong I σ g → FinalTheorems.EffCartier I → ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  first | exact @GlobalTheory.ProjBlowup.exists_proportional | exact GlobalTheory.ProjBlowup.exists_proportional | (intros; apply GlobalTheory.ProjBlowup.exists_proportional <;> assumption)
end

