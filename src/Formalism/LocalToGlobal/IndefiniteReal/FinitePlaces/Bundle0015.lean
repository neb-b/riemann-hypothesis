module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNatSmulMem
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

lemma uniform_nat {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i k m, P i k → P i (m * k))
    (h : ∀ i, ∃ k, 0 < k ∧ P i k) : ∃ k, 0 < k ∧ ∀ i, P i k := by
  classical
  choose k hk hPk using h
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hPk i)

lemma selfDual_isFullLattice (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

lemma exists_nat_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : Fin n → D.host.E) :
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem hΛ x

lemma exists_nat_smul_single {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
  refine uniform_nat (fun j m => (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ) (fun j k m h => ?_)
    (fun j => exists_nat_smul_mem hΛ _)
  rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact Λ.nsmul_mem h m

lemma exists_nat_denom {n : ℕ} (v : Fin n → D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  uniform_nat (fun j c => (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun j k m h => by push_cast; rw [mul_assoc]; exact mul_mem (natCast_mem _ m) h)
    (fun j => by obtain ⟨m, hm, h⟩ := exists_nat_mul_mem (v j); exact ⟨m, hm, h⟩)

theorem lattice_projective {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) : Module.Projective (𝓞 D.host.E) Λ := by
  have : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have : Module.Flat (𝓞 D.host.E) Λ := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    rw [Submodule.mem_bot]
    rw [Submonoid.smul_def] at ha
    exact (smul_eq_zero.1 ha).resolve_left (nonZeroDivisors.coe_ne_zero a)
  have : Module.FinitePresentation (𝓞 D.host.E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem hF_eq_dot (S : HSp D) (x y : Fin S.rank → D.host.E) :
    hF S x y = (fun a => star (x a)) ⬝ᵥ (S.gram *ᵥ y) := by
  simp only [hF, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hF_swap (S : HSp D) (x y : Fin S.rank → D.host.E) : hF S x y = star (hF S y x) := by
  unfold hF
  simp only [star_sum, star_mul', star_star, star_gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def repV (S : HSp D) (w : Fin S.rank → D.host.E) : Fin S.rank → D.host.E :=
  fun k => star ((w ᵥ* S.gram⁻¹) k)

theorem hF_repV (S : HSp D) (w v : Fin S.rank → D.host.E) : hF S (repV S w) v = w ⬝ᵥ v := by
  have h1 : S.gram⁻¹ * S.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))
  have h2 : (fun a => star (repV S w a)) = w ᵥ* S.gram⁻¹ := by
    funext a; simp [repV]
  rw [hF_eq_dot, h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]


set_option maxHeartbeats 1600000 in
theorem selfDual_basis (S : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S ΛS) :
    ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v := by
  classical
  have := lattice_projective hS.1
  have : Module.Finite (𝓞 D.host.E) ΛS := Module.Finite.iff_fg.2 hS.1.fg
  obtain ⟨N, f, hf⟩ := Module.Finite.exists_fin' (𝓞 D.host.E) ΛS
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  let gg : Fin N → ΛS := fun i => f (fun j => if i = j then 1 else 0)
  have hrep : ∀ x : ΛS, ∑ i, σ x i • gg i = x := by
    intro x
    have h1 : f (σ x) = x := LinearMap.congr_fun hσ x
    have h2 : f (σ x) = ∑ i, σ x i • gg i := by
      conv_lhs => rw [pi_eq_sum_univ (σ x)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, gg]
    rw [← h2, h1]
  let A := algebraMap (𝓞 D.host.E) D.host.E
  obtain ⟨m, hm, hmS⟩ := exists_nat_smul_single (selfDual_isFullLattice S ΛS hS)
  have hm0 : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let em : Fin S.rank → ΛS := fun j => ⟨(m : D.host.E) • (Pi.single j 1 : Fin S.rank → D.host.E), hmS j⟩
  let w : Fin N → Fin S.rank → D.host.E := fun i j => A (σ (em j) i) / m
  have hw : ∀ i j, A (σ (em j) i) = m * w i j := by
    intro i j; simp only [w]; field_simp

  have hagree : ∀ (x : ΛS) (i : Fin N), A (σ x i) = w i ⬝ᵥ (x : Fin S.rank → D.host.E) := by
    intro x i
    obtain ⟨c, hc, hcx⟩ := exists_nat_denom (x : Fin S.rank → D.host.E)
    have hcx' : ∀ j, ∃ y, A y = (c : D.host.E) * (x : Fin S.rank → D.host.E) j := fun j => RingHom.mem_range.1 (hcx j)
    choose o ho using hcx'
    have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
    have hx : ((c * m : ℕ) : 𝓞 D.host.E) • x = ∑ j, o j • em j := by
      apply Subtype.ext
      funext k
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, em]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def]
      have := ho k
      simp only [A] at this
      rw [map_natCast, this]
      push_cast; ring
    have h3 := congrArg (fun y => A (σ y i)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_natCast] at h3
    apply mul_left_cancel₀ (mul_ne_zero hc0 hm0)
    rw [dotProduct, Finset.mul_sum]
    have e1 : ((c * m : ℕ) : D.host.E) = (c : D.host.E) * m := by push_cast; ring
    rw [e1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho j, hw i j]; ring

  have hcol : ∀ j, ∑ i, w i j • (gg i : Fin S.rank → D.host.E) = Pi.single j 1 := by
    intro j
    have h := congrArg (fun y : ΛS => (y : Fin S.rank → D.host.E)) (hrep (em j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    have h' : ∑ i, A (σ (em j) i) • (gg i : Fin S.rank → D.host.E) = (m : D.host.E) • Pi.single j 1 :=
      (Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E _ _).trans h
    simp only [hw, mul_smul, ← Finset.smul_sum] at h'
    exact smul_right_injective _ hm0 h'
  refine ⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => repV S (w i), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩
  · refine (hS.2 (repV S (w i))).2 fun x hx => ⟨starO (σ ⟨x, hx⟩ i), ?_⟩
    rw [coe_starO]
    show star (A (σ ⟨x, hx⟩ i)) = hF S x (repV S (w i))
    rw [hF_swap, hF_repV, hagree]
  · simp only [hF_repV, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, (w i j * v j) • (gg i : Fin S.rank → D.host.E)
        = ∑ j, v j • ∑ i, w i j • (gg i : Fin S.rank → D.host.E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ j, v j • (Pi.single j 1 : Fin S.rank → D.host.E) := by simp only [hcol]
      _ = v := by
          funext k
          simp [Finset.sum_apply, Pi.single_apply]

end Formalism.IndefR.Fin.PDA

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.GlobalDualOfBasis
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct Pointwise

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem xi_AA_AAbar : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA *
    D.host.AAbar = FractionalIdeal.dual ℤ ℚ 1 := by
  have hfp := factPrincipalDatum D.R D.host
  have hdd := coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)
  have := eq_inv_of_mul_eq_one_left hfp
  rw [this]
  show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _
  rw [hdd, inv_inv]

theorem one_ne_zero' : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot

theorem dual_ne_zero' : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero'

theorem AA_ne_zero : D.host.AA ≠ 0 := by
  intro h0
  have h := xi_AA_AAbar (D := D)
  rw [h0, mul_zero, zero_mul] at h
  exact dual_ne_zero' h.symm


set_option maxHeartbeats 800000 in
theorem mem_AA_of_trace {z : D.host.E}
    (h : ∀ c ∈ D.host.AA, Algebra.trace D.host.F D.host.E (D.host.xi0 * (star c * z)) ∈ invDiff D.host.F) :
    z ∈ D.host.AA := by
  have hX := xi_AA_AAbar (D := D)
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero'
  have hmem : ∀ j ∈ D.host.AAbar, D.host.xi0 * z * j ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro j hj
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    have hc : D.host.conj j ∈ D.host.AA := Formalism.L2.Pj.conj_mem_AA D hj
    have hco : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) ∈ D.host.AA := by
      have e : D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o) = starO o • D.host.conj j := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [e]; exact Submodule.smul_mem _ _ hc
    obtain ⟨k, hk⟩ := h _ hco 1
    rw [show ((1 : 𝓞 D.host.F) : D.host.F) = 1 from rfl, mul_one] at hk
    have hs : star (D.host.conj j) = j := by
      rw [Formalism.BasicNotions.Examples₂.star_eq_conj, Formalism.MainNotions.UnusedSlot33.HK.conj_conj]
    have he : D.host.xi0 * (star (D.host.conj j * star (algebraMap (𝓞 D.host.E) D.host.E o)) * z) =
        D.host.xi0 * z * j * algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [star_mul', star_star, hs]; ring
    rw [he] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := D.host.F), hk, eq_intCast]
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 * z) * D.host.AAbar ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r (hmem j hj)
  set Y := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AAbar with hYdef
  have hAY : D.host.AA * Y = FractionalIdeal.dual ℤ ℚ 1 := by rw [← hX, hYdef]; ring
  have hY : Y ≠ 0 := by
    have h0 : D.host.AA * Y ≠ 0 := by rw [hAY]; exact dual_ne_zero'
    exact right_ne_zero_of_mul h0
  have hzY : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y ≤ D.host.AA * Y := by
    rw [hAY, hYdef, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm z]
    exact hle
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z ≤ D.host.AA :=
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) z * Y * Y⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
      _ ≤ D.host.AA * Y * Y⁻¹ := by gcongr
      _ = D.host.AA := by rw [mul_assoc, mul_inv_cancel₀ hY, mul_one]
  exact hsp (FractionalIdeal.mem_spanSingleton_self _ _)

theorem hF_smul_right (T : HSp D) (x v : Fin T.rank → D.host.E) (j : D.host.E) :
    hF T x (j • v) = j * hF T x v := by
  unfold hF
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ind_of_hF {T : HSp D} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    {v : Fin T.rank → D.host.E} (hv : ∀ t ∈ ΛT, hF T t v ∈ D.host.AA) (P : (Fin T.rank → D.host.E) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hgen : ∀ a ∈ D.host.AA, ∀ t ∈ ΛT, P (a • t)) : P v := by
  have hA := AA_ne_zero (D := D)
  have key : ∀ x ∈ D.host.AA * D.host.AA⁻¹, P (x • v) := by
    intro x hx
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro i hi j hj
      have hjv : j • v ∈ ΛT := by
        refine (hT.2 (j • v)).2 fun t ht => ?_
        have hm : j * hF T t v ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hj (hv t ht)
        rw [inv_mul_cancel₀ hA] at hm
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hm
        refine ⟨b, ?_⟩
        rw [show (b : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b from rfl, hb, ← hF_smul_right]
        rfl
      rw [mul_smul]
      exact hgen i hi _ hjv
    · intro x y hx hy
      rw [add_smul]
      exact hadd _ _ hx hy
  have h1 : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
    rw [mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  simpa using key 1 h1

abbrev rkSpan (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Submodule ℤ (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t}

theorem hF_mulVec (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ∑ cc, ∑ d, star (t cc) * T.gram cc d * ∑ a, γ d a * s a = hF T t (γ.mulVec s) := by
  unfold hF
  simp only [Matrix.mulVec, dotProduct]

theorem globalDual_of_basis (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hT : IsSelfDualC T ΛT)
    (hB : ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (h : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) :
    γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t} := by
  obtain ⟨N, g, s', hg, hs', hid⟩ := hB
  have h1 : ∀ s ∈ ΛS, ∀ t ∈ ΛT, hF T t (γ.mulVec s) ∈ D.host.AA := by
    intro s hs t ht
    apply mem_AA_of_trace
    intro c hc
    have := h c hc s hs t ht
    unfold betaO at this
    rwa [hermitian_rank_one_right, hF_mulVec] at this
  have h2 : ∀ s ∈ ΛS, ∀ v : Fin T.rank → D.host.E, (∀ t ∈ ΛT, hF T t v ∈ D.host.AA) →
      rk1 S T 1 s v ∈ rkSpan S T ΛS ΛT := by
    intro s hs v hv
    refine ind_of_hF hT hv (fun w => rk1 S T 1 s w ∈ rkSpan S T ΛS ΛT) ?_ ?_ ?_
    · have : rk1 S T 1 s 0 = 0 := by ext i j; simp [rk1]
      simp only [this]; exact zero_mem _
    · intro x y hx hy
      have : rk1 S T 1 s (x + y) = rk1 S T 1 s x + rk1 S T 1 s y := by
        ext i j; simp only [rk1, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; ring
      simp only [this]; exact add_mem hx hy
    · intro a ha t ht
      have : rk1 S T 1 s (a • t) = rk1 S T a s t := by
        ext i j; simp only [rk1, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]; ring
      simp only [this]
      exact Submodule.subset_span ⟨a, ha, s, hs, t, ht, rfl⟩
  have h3 : γ = ∑ i, rk1 S T 1 (s' i) (γ.mulVec (g i)) := by
    refine Matrix.ext fun a j => ?_
    have hj : γ.mulVec (∑ i, hF S (s' i) (Pi.single j 1) • g i) a = γ.mulVec (Pi.single j 1) a :=
      congrArg (fun w => γ.mulVec w a) (hid (Pi.single j 1))
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hj
    rw [← hj]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.sum_apply, rk1, Matrix.of_apply, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : hF S (s' i) (Pi.single j 1) = ∑ k, star (s' i k) * S.gram k j := by
      unfold hF
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Pi.single_apply]
    rw [e]; ring
  rw [h3]
  exact Submodule.sum_mem _ fun i _ => h2 (s' i) (hs' i) _ fun t ht => h1 (g i) (hg i) t ht

end Formalism.IndefR.Fin.PDA

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


set_option maxHeartbeats 800000 in
theorem lat_ann (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ψ (symplO S T x u) = 1 := by
  have inner : ∀ {α : Af D.host.F} {c : D.host.E} {s : Fin S.rank → D.host.E} {t : Fin T.rank → D.host.E},
      α ∈ intAf D.host.F → c ∈ D.host.AA → s ∈ ΛS → t ∈ ΛT →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 α • ratW T S (rk1 S T c s t)) u) = 1 := by
    intro α c s t hα hc hs ht u hu
    induction hu using AddSubgroup.closure_induction with
    | mem u' hu' =>
      obtain ⟨α', hα', -, c', hc', s', hs', t', ht', rfl⟩ := hu'
      rw [gen_eq]
      exact psi_gen hψ S T hS hT hα hα' hc hc' hs hs' ht ht'
    | zero => rw [symplO_zero_right, AddChar.map_zero_eq_one]
    | add u1 u2 _ _ h1 h2 => rw [symplO_add_right, AddChar.map_add_eq_mul, h1, h2, one_mul]
    | neg u' _ h => rw [symplO_neg_right, AddChar.map_neg_eq_inv, h, inv_one]
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx'
    rw [gen_eq]
    exact inner hα hc hs ht u hu
  | zero => rw [symplO_zero_left, AddChar.map_zero_eq_one]
  | add x1 x2 _ _ h1 h2 => rw [symplO_add_left, AddChar.map_add_eq_mul, h1, h2, one_mul]
  | neg x' _ h => rw [symplO_neg_left, AddChar.map_neg_eq_inv, h, inv_one]

end Formalism.IndefR.Fin

end
end

