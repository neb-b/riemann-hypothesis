module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParity
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem zmf_congr_cop {k l : ℕ} (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hp
  · rfl
  · push_neg at hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    have hx' : ¬ l ∣ x.1 := fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)
    have hy' : ¬ l ∣ y.2 := fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)
    rw [h _ _ hx' hy']

theorem zmf_sum_smul {ι : Type*} (s : Finset ι) (k l : ℕ) (u v : ℤ → ℂ) (c : ι → ℂ) (G : ι → ℕ → ℕ → ℂ) :
    Zm k l u v (fun x y => ∑ i ∈ s, c i * G i x y) = ∑ i ∈ s, c i • Zm k l u v (G i) := by
  funext n
  simp only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem zmf_mf_sum {ι : Type*} (s : Finset ι) (k L : ℕ) (χ : ℤ → ℂ) (g : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, MF k L χ (g i)) : MF k L χ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (_root_.GlobalTheory.EisM.mf_linear k L χ).1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((_root_.GlobalTheory.EisM.mf_linear k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1

theorem zm_fun_mf : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  intro k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set φ : ℂ := ((l ^ m).totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'
  set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc
  have hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ),
      ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹) := by
    intro ψ u; rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w := by
    intro w
    calc f w = φ⁻¹ * (f w * φ) := by field_simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * (if (u : ZMod (l ^ m)) = w then φ else 0) := by
          congr 1
          simp only [Units.val_inj, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']; simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
      _ = ∑ ψ, c ψ * ψ w := by
          simp only [hc, hinv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_
          ring
  have hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν)
      (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0)) := by
    apply zmf_congr_cop
    intro x y hx hy
    have cx : Nat.Coprime x (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm
    have cy : Nat.Coprime y (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm
    set ux := ZMod.unitOfCoprime x cx
    set uy := ZMod.unitOfCoprime y cy
    have ex : ((x : ℤ) : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey : ((y : ℤ) : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    have ex' : (x : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey' : (y : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    simp only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]
    rw [ZMod.inv_coe_unit, ← Units.val_mul, hexp]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← map_mul, ← Units.val_mul]
  rw [hquo, zmf_sum_smul]
  apply zmf_mf_sum
  intro ψ _
  have hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1 := by
    intro M χ; rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hh := (_root_.GlobalTheory.EisM.hat_char_props).1 N θ hN
  by_cases hψ : ψ (-1) = θ (-1)
  · have h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0) := by
      obtain ⟨r, rfl⟩ := hodd
      rw [hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num
    have h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1) := by
      rw [hψ, hν, mul_neg, hsq]; norm_num
    exact ((_root_.GlobalTheory.EisM.mf_linear k _ (ch ε)).2.2.1 (c ψ) _
      (_root_.GlobalTheory.zm_char_mf k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1
  · have hc0 : c ψ = 0 := by
      have hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1 := by
        intro M χ
        have := hsq χ
        have h' : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.1 h' with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hprod : θ (-1) * ψ⁻¹ (-1) = -1 := by
        have hi : ψ⁻¹ (-1) = ψ (-1) := by
          rw [MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]
        rw [hi]
        rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢
        all_goals first | exact absurd rfl hψ | norm_num
      set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS
      have hS' : S = - S := by
        calc S = ∑ u : (ZMod (l ^ m))ˣ, f ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * ψ⁻¹ ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) :=
              (Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)).symm
          _ = ∑ u : (ZMod (l ^ m))ˣ, (θ (-1) * ψ⁻¹ (-1)) * (f u * ψ⁻¹ u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]
              ring
          _ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]
      have : S = 0 := by linear_combination hS' / 2
      simp [hc, ← hS, this]
    rw [hc0, zero_smul]
    exact (_root_.GlobalTheory.EisM.mf_linear k _ (ch ε)).1

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ListFormLabels
section
open Polynomial

noncomputable section

namespace GlobalTheory.Proof.ListFormLabels

open Formalism.BasicNotions

def ListFormAt (D : D7) (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∃ L : List (ℕ × ℕ × Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = D.ntypes.bc σ ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ D.host.g k) = p.2.2) ∧
      Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v) = (L.map fun p => p.2.1 • p.2.2).sum) ∧
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : Formalism.MainNotions.N.GE D.nd,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

end GlobalTheory.Proof.ListFormLabels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BKDimNoInv

section Bridge

open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x :=
  rfl

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem toLL_continuous : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem rep_continuous {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (x : Fin m → ↥Bw.LL.1) : Continuous fun g => Bw.rep r g x := by
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  simp only [rep_apply]
  exact ((hr.comp Bw.e_symm_cont).matrix_map (toLL_continuous Bw)).matrix_mulVec continuous_const

theorem localGaloisRep_invariants_from_fractionRing [IsDomain O] {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) : H0V (Bw.rep r) = ⊥ := by
  obtain ⟨_, -, hfr⟩ := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.1
  let φ : FractionRing O →+* ↥Bw.LL.1 := IsFractionRing.lift (g := Bw.toLL) (toLL_injective Bw)
  have hφ : ∀ a, φ (algebraMap O _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap _ a
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(OL Bw.LL)) y
    refine ⟨algebraMap O _ (Bw.eO.symm n) / algebraMap O _ (Bw.eO.symm d), ?_⟩
    rw [map_div₀, hφ, hφ]
    simp [LocBridge.toLL]
  rw [eq_bot_iff]
  intro x hx
  choose x₀ hx₀ using fun a => hsurj (x a)
  have h0 : x₀ = 0 := by
    refine h x₀ fun g => ?_
    have h1 : Bw.rep r (Bw.e g) x = x := by
      have := (Submodule.mem_iInf _).1 hx (Bw.e g)
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [rep_apply, MulEquiv.symm_apply_apply] at h1
    funext a
    apply φ.injective
    rw [hx₀, ← congrFun h1 a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hφ, hx₀]
  rw [Submodule.mem_bot]
  funext a
  rw [← hx₀, h0]
  exact map_zero φ

noncomputable def grepOf {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) :=
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  { V := Fin m → ↥Bw.LL.1
    acg := inferInstance
    modLL := inferInstance
    modQp := inferInstance
    towQp := inferInstance
    modO := inferInstance
    towO := inferInstance
    fd := inferInstance
    top := inferInstance
    mtop := inferInstance
    cadd := inferInstance
    csmul := inferInstance
    ρ := Bw.rep r
    cont := rep_continuous Bw r hr }


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem finrank_h1f_no_invariants [IsDomain O] (P : LocPrime l) {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hBK : Formalism.MainNotions.LocalSituation.bkADim (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) :
    (Module.finrank ↥Bw.LL.1 (FiniteCohomology (P.PD Bw.Kw) (Bw.rep r)) : ℤ) =
      (Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) : ℤ) -
        Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r) ⊓
          FilV (P.PD Bw.Kw) (LL := ↥Bw.LL.1) (V := Fin m → ↥Bw.LL.1) 0) := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  have key := hBK _ _ hG A hA
  have h0 : Module.finrank ↥Bw.LL.1 ↥(H0V A.ρ) = 0 := by
    have : H0V A.ρ = ⊥ := localGaloisRep_invariants_from_fractionRing Bw r h
    rw [this, finrank_bot]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key

end Bridge

end GlobalTheory.BKDimNoInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestWeightGeneratedFiltration
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FockGrade

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_Eab_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (a b c d : Ix p q) (x : V) :
    act (Eab a b) (act (Eab c d) x) = act (Eab c d) (act (Eab a b) x) +
      (if b = c then act (Eab a d) x else 0) - (if d = a then act (Eab c b) x else 0) := by
  have h1 := congrArg (fun f : Module.End ℂ V => f x) (h (Eab a b) (Eab c d))
  simp only [map_sub, LinearMap.sub_apply, Module.End.mul_apply] at h1
  have e1 : act (Eab a b * Eab c d) x = if b = c then act (Eab a d) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  have e2 : act (Eab c d * Eab a b) x = if d = a then act (Eab c b) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  rw [← e1, ← e2, add_sub_assoc, h1]; abel

def layer (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  Nat.rec W (fun _ N => ⨆ ab : Fin p × Fin q, N.map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2)))) m

theorem layer_succ (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) :
    layer act W (m + 1) =
      ⨆ ab : Fin p × Fin q, (layer act W m).map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2))) := rfl

theorem raise_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} (a : Fin p) (b : Fin q)
    {y : V} (hy : y ∈ layer act W m) : act (Eab (Sum.inl a) (Sum.inr b)) y ∈ layer act W (m + 1) :=
  Submodule.mem_iSup_of_mem (a, b) (Submodule.mem_map_of_mem hy)

theorem layer_succ_le {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} {S : Submodule ℂ V}
    (h : ∀ a b, ∀ y ∈ layer act W m, act (Eab (Sum.inl a) (Sum.inr b)) y ∈ S) : layer act W (m + 1) ≤ S := by
  refine iSup_le fun ab => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h _ _ y hy

theorem layer_finite {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} (hW : FiniteDimensional ℂ W)
    (m : ℕ) : FiniteDimensional ℂ (layer act W m) := by
  induction m with
  | zero => exact hW
  | succ m ih => rw [layer_succ]; infer_instance

theorem layer_compact {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (m : ℕ) : ∀ a b, sameBlock a b → ∀ y ∈ layer act W m,
      act (Eab a b) y ∈ layer act W m := by
  induction m with
  | zero => intro a b hab y hy; exact hK _ (GlobalTheory.FockTensor.isKC_Eab hab) y hy
  | succ m ih =>
    intro a b hab
    have : layer act W (m + 1) ≤ (layer act W (m + 1)).comap (act (Eab a b)) := by
      refine layer_succ_le fun i j y hy => ?_
      rw [Submodule.mem_comap, act_Eab_comm h]
      refine sub_mem (add_mem (raise_mem _ _ (ih a b hab y hy)) ?_) ?_
      · split_ifs with hb
        · subst hb
          rcases a with a | a
          · exact raise_mem _ _ hy
          · exact absurd hab (by simp [sameBlock])
        · exact zero_mem _
      · split_ifs with hb
        · subst hb
          rcases b with b | b
          · exact absurd hab (by simp [sameBlock])
          · exact raise_mem _ _ hy
        · exact zero_mem _
    exact fun y hy => this hy

theorem sup_stable_of {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {f : Module.End ℂ V}
    (hf : ∀ m, ∀ y ∈ layer act W m, f y ∈ ⨆ m, layer act W m) :
    ∀ y ∈ ⨆ m, layer act W m, f y ∈ ⨆ m, layer act W m := by
  have : (⨆ m, layer act W m) ≤ (⨆ m, layer act W m).comap f := iSup_le fun m y hy => hf m y hy
  exact fun y hy => this hy

theorem sup_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (hL : ∀ e ∈ W, KilledByLower act e) (a b : Ix p q) :
    ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m := by
  have hk : ∀ a b, sameBlock a b → ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m :=
    fun a b hab => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem m (layer_compact h hK m a b hab y hy)
  have hr : ∀ a b, ∀ y ∈ ⨆ m, layer act W m,
      act (Eab (Sum.inl a) (Sum.inr b)) y ∈ ⨆ m, layer act W m :=
    fun a b => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem (m + 1) (raise_mem a b hy)
  rcases a with a | a <;> rcases b with b | b
  · exact hk _ _ trivial
  · exact hr _ _
  · refine sup_stable_of fun m => ?_
    induction m with
    | zero => intro y hy; rw [hL y hy b a]; exact zero_mem _
    | succ m ih =>
      have : layer act W (m + 1) ≤ (⨆ m, layer act W m).comap (act (Eab (Sum.inr a) (Sum.inl b))) := by
        refine layer_succ_le fun i j y hy => ?_
        have hy' : y ∈ ⨆ m, layer act W m := Submodule.mem_iSup_of_mem m hy
        rw [Submodule.mem_comap, act_Eab_comm h]
        refine sub_mem (add_mem (hr _ _ _ (ih y hy)) ?_) ?_
        · split_ifs
          · exact hk (Sum.inr a) (Sum.inr j) trivial _ hy'
          · exact zero_mem _
        · split_ifs
          · exact hk (Sum.inl i) (Sum.inl b) trivial _ hy'
          · exact zero_mem _
      exact fun y hy => this hy
  · exact hk _ _ trivial

theorem layer_eigen {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V} {c : ℂ}
    (hc : ∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) (m : ℕ) :
    ∀ x ∈ layer act W m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  induction m with
  | zero => intro x hx; simpa using hc x hx
  | succ m ih =>
    have : layer act W (m + 1) ≤ LinearMap.ker ((∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i))) -
        (c + ((m + 1 : ℕ) : ℂ)) • (LinearMap.id : V →ₗ[ℂ] V)) := by
      refine layer_succ_le fun a b y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      have e : ∀ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) (act (Eab (Sum.inl a) (Sum.inr b)) y) =
          act (Eab (Sum.inl a) (Sum.inr b)) (act (Eab (Sum.inl i) (Sum.inl i)) y) +
            (if i = a then act (Eab (Sum.inl a) (Sum.inr b)) y else 0) := by
        intro i
        rw [act_Eab_comm h]
        by_cases hi : i = a
        · subst hi; simp
        · simp [hi]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e, Finset.sum_add_distrib, ← map_sum, ih y hy]
      simp [add_smul, add_assoc]
    intro x hx
    have h2 := this hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero] at h2
    simpa using h2

theorem exists_grading : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (W : Submodule ℂ V) (c : ℂ), FiniteDimensional ℂ W → KStable act W → (∀ e ∈ W, KilledByLower act e) → (∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) → ∃ N : ℕ → Submodule ℂ V, N 0 = W ∧ (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = genSub act (W : Set V) ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  intro p q V _ _ act h W c hW hK hL hc
  refine ⟨layer act W, rfl, layer_finite hW, le_antisymm ?_ ?_, layer_eigen h hc⟩
  · refine iSup_le fun m => le_sInf fun S hS => ?_
    induction m with
    | zero => exact hS.1
    | succ m ih => exact layer_succ_le fun a b y hy => hS.2 _ _ (ih hy)
  · refine sInf_le ⟨fun x hx => Submodule.mem_iSup_of_mem 0 hx, fun Z y hy => ?_⟩
    have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    rw [hZ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (sup_stable h hK hL a b y hy)

end GlobalTheory.FockGrade
end
end

