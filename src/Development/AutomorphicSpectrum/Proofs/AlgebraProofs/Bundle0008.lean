module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0002
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.CharExt

variable {R : Type} [CommRing R] {T : Type} [CommGroup T] [Fintype T]
variable (K : Type) [Field K] [Algebra R K]

def dualOrder (A : Subalgebra R (T → R)) : Submodule R (T → K) where
  carrier := {l | ∀ f ∈ A, ∃ r : R, algebraMap R K r = ∑ t, l t * algebraMap R K (f t)}
  add_mem' := by
    rintro a b ha hb f hf
    obtain ⟨r, hr⟩ := ha f hf
    obtain ⟨s, hs⟩ := hb f hf
    exact ⟨r + s, by simp [add_mul, Finset.sum_add_distrib, hr, hs]⟩
  zero_mem' := fun f _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ha f hf
    obtain ⟨r, hr⟩ := ha f hf
    exact ⟨c * r, by simp [map_mul, hr, Finset.mul_sum, Algebra.smul_def, mul_assoc]⟩

variable {K}

def conv (l m : T → K) : T → K := fun t => ∑ x, l x * m (x⁻¹ * t)

lemma sum_conv_mul (l m g : T → K) :
    ∑ t, conv l m t * g t = ∑ x, ∑ y, l x * m y * g (x * y) := by
  simp only [conv, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun t => by simp)

lemma conv_mem {A : Subalgebra R (T → R)} (hc : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A)
    {l m : T → K} (hl : l ∈ dualOrder K A) (hm : m ∈ dualOrder K A) : conv l m ∈ dualOrder K A := by
  intro f hf
  have key : ∀ g ∈ prodSpan A, ∃ r : R, algebraMap R K r =
      ∑ x, ∑ y, l x * m y * algebraMap R K (g (x, y)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨r, hr⟩ := hl a ha
      obtain ⟨s, hs⟩ := hm b hb
      refine ⟨r * s, ?_⟩
      rw [map_mul, hr, hs, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [map_mul]; ring
    | zero => exact ⟨0, by simp⟩
    | add g h _ _ hg hh =>
      obtain ⟨r, hr⟩ := hg
      obtain ⟨s, hs⟩ := hh
      refine ⟨r + s, ?_⟩
      simp [hr, hs, mul_add, Finset.sum_add_distrib]
    | smul c g _ hg =>
      obtain ⟨r, hr⟩ := hg
      refine ⟨c * r, ?_⟩
      simp only [map_mul, hr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
  obtain ⟨r, hr⟩ := key _ (hc f hf)
  refine ⟨r, ?_⟩
  rw [hr, sum_conv_mul l m (fun t => algebraMap R K (f t))]


open Classical in
noncomputable def psi {A : Subalgebra R (T → R)} (d : R) (hd : ∀ f : T → R, d • f ∈ A) :
    Module.Dual R A →ₗ[R] (T → K) := by
  classical
  exact {
    toFun := fun l t => algebraMap R K (l ⟨d • Pi.single t 1, hd _⟩) / algebraMap R K d
    map_add' := by intros; ext; simp [add_div]
    map_smul' := by intros; ext; simp [mul_div_assoc, Algebra.smul_def] }

lemma psi_pair [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A)
    (l : Module.Dual R A) (f : T → R) (hf : f ∈ A) :
    ∑ t, psi (K := K) d hd l t * algebraMap R K (f t) = algebraMap R K (l ⟨f, hf⟩) := by
  classical
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
  have e : d • (⟨f, hf⟩ : A) = ∑ t, f t • (⟨d • Pi.single t 1, hd _⟩ : A) := by
    apply Subtype.ext
    funext s
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have e2 := congrArg (fun a => algebraMap R K (l a)) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, map_mul] at e2
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [eq_comm, ← mul_right_inj' hdK, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  field_simp

lemma range_psi [FaithfulSMul R K] {A : Subalgebra R (T → R)} {d : R} (hd0 : d ≠ 0) (hd : ∀ f : T → R, d • f ∈ A) :
    LinearMap.range (psi (K := K) d hd) = dualOrder K A := by
  classical
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdK : algebraMap R K d ≠ 0 := by simpa using hinj.ne hd0
  apply le_antisymm
  · rintro _ ⟨l, rfl⟩ f hf
    exact ⟨l ⟨f, hf⟩, (psi_pair hd0 hd l f hf).symm⟩
  · intro l hl
    choose L hL using fun f : A => hl f.1 f.2
    let L' : Module.Dual R A :=
      { toFun := L
        map_add' := fun a b => hinj (by
          simp [hL, add_mul, mul_add, Finset.sum_add_distrib])
        map_smul' := fun c a => hinj (by
          simp [hL, Finset.mul_sum, mul_left_comm]) }
    refine ⟨L', ?_⟩
    funext t
    simp only [psi, LinearMap.coe_mk, AddHom.coe_mk]
    change algebraMap R K (L _) / _ = _
    rw [hL]
    simp [Pi.single_apply, div_eq_iff hdK, apply_ite (algebraMap R K)]

def pairWith (c : T → K) : (T → K) →ₗ[R] K where
  toFun l := ∑ t, l t * c t
  map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum, Algebra.smul_def, mul_assoc]

lemma pairWith_conv {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (l m : T → K) :
    pairWith (R := R) c (conv l m) = pairWith (R := R) c l * pairWith (R := R) c m := by
  simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_conv_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hc]; ring

lemma isIntegral_pairWith [FaithfulSMul R K] {A : Subalgebra R (T → R)} (hA : IsHopfOrder A)
    {c : T → K} (hc : ∀ x y, c (x * y) = c x * c y) (hc1 : c 1 = 1)
    {l : T → K} (hl : l ∈ dualOrder K A) : IsIntegral R (pairWith (R := R) c l) := by
  classical
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  have hfg : (dualOrder K A).FG := by
    rw [← range_psi hd0 hd]
    rw [← Submodule.map_top]
    exact (Module.Finite.fg_top (R := R) (M := Module.Dual R A)).map _
  let M : Submodule R K := (dualOrder K A).map (pairWith (R := R) c)
  have hone : (1 : K) ∈ M := by
    refine ⟨Pi.single 1 1, ?_, ?_⟩
    · intro f _
      exact ⟨f 1, by simp [Pi.single_apply]⟩
    · simp [pairWith, Pi.single_apply, hc1]
  have hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨conv a b, conv_mem hA.comul ha hb, pairWith_conv hc a b⟩
  let S : Subalgebra R K := M.toSubalgebra hone (fun x y hx hy => hmul x hx y hy)
  exact IsIntegral.of_mem_of_fg S (by simpa [S] using hfg.map _) _ ⟨l, hl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.BT.CharExt

open GlobalTheory.CompanionTheory.Ar.BT.CharExt

open GlobalTheory.CompanionTheory.Ar.BT.CharExt in
theorem GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A →
    ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  intro R _ _ T _ _ _ A hA χ
  classical
  cases nonempty_fintype T
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hinj
  obtain ⟨d, hd0, hd⟩ := hA.full
  haveI := hA.finite
  haveI := hA.projective
  obtain ⟨n, p, g, hp, hg, hpg⟩ := Module.Finite.exists_comp_eq_id_of_projective R A
  set c : T → R := fun t => ((χ t : Rˣ) : R) with hcdef
  let cK : T → K := fun t => algebraMap R K (c t)
  have hmul : ∀ x y, cK (x * y) = cK x * cK y := by
    intro x y; simp [cK, c]
  have h1 : cK 1 = 1 := by simp [cK, c]
  let x : A := ⟨d • c, hd c⟩
  have hr : ∀ i : Fin n, ∃ r : R, g x i = d * r := by
    intro i
    let li : Module.Dual R A := (LinearMap.proj i).comp g
    have hl : psi (K := K) d hd li ∈ dualOrder K A := by
      rw [← range_psi hd0 hd]; exact ⟨li, rfl⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_pairWith hA hmul h1 hl)
    refine ⟨r, hinj ?_⟩
    have := psi_pair (K := K) hd0 hd li (d • c) (hd c)
    change _ = algebraMap R K (li x) at this
    change algebraMap R K (li x) = _
    rw [← this, map_mul, hr]
    simp only [pairWith, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, cK]
    ring
  choose r hr using hr
  have hx : p (g x) = x := by
    have := LinearMap.congr_fun hpg x
    simpa using this
  rw [LinearMap.pi_apply_eq_sum_univ p (g x)] at hx
  simp only [hr, mul_smul, ← Finset.smul_sum] at hx
  have hc : c = ((∑ i, r i • p (fun j => if i = j then 1 else 0) : A) : T → R) := by
    funext t
    have e := congrArg (fun a : A => (a : T → R) t) hx
    apply mul_left_cancel₀ hd0
    exact e.symm
  rw [hc]
  exact Subtype.property _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNorm
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_extension_kernel_bound_charpoly : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  exact @PositivityTheory.Xgn.kernel_rank_norm_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
section
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type*} [AddCommGroup E] [Module Ω E]

theorem exists_pow_cover {k : ℕ} (f c : Fin k → R) (h : ∑ l, c l * f l = 1) (n : ℕ) :
    ∃ d : Fin k → R, ∑ l, d l * f l ^ n = 1 := by
  have h1 : Ideal.span (Set.range f) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← h]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
  exact h2

theorem exists_charts {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (f c : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E), ∑ l, c l * f l = 1 ∧
      (∀ l q, ∃ n : ℕ, (f l : Ω) ^ n • B l q ∈ L) ∧
      ∀ l q, ∀ e ∈ L, ∃ n : ℕ, (f l : Ω) ^ n * (B l).repr e q ∈ R := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hs, hb⟩ := h
  choose b hli hsp hiff using hb
  refine ⟨k, fun l => ⟨f l, hf l⟩, fun l => ⟨c l, hc l⟩,
    fun l => Module.Basis.mk (hli l) (hsp l).ge, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hs
  · intro l q
    rw [Module.Basis.mk_apply]
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  · intro l q e he
    obtain ⟨a, ha, rfl⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n, ?_⟩
    have : (Module.Basis.mk (hli l) (hsp l).ge).repr (∑ q, a q • b l q) q = a q := by
      have h2 : (∑ q, a q • b l q) = ∑ q, a q • (Module.Basis.mk (hli l) (hsp l).ge) q := by
        simp [Module.Basis.mk_apply]
      rw [h2, Module.Basis.repr_sum_self]
    rw [this]
    exact hn

theorem pow_smul_mem {L : Submodule R E} (f : R) {n m : ℕ} (hnm : n ≤ m) {e : E}
    (h : (f : Ω) ^ n • e ∈ L) : (f : Ω) ^ m • e ∈ L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  have := L.smul_mem (f ^ j) h
  rw [pow_add, mul_smul]
  simpa [Subalgebra.smul_def] using this

theorem pow_mul_mem (f : R) {n m : ℕ} (hnm : n ≤ m) {a : Ω}
    (h : (f : Ω) ^ n * a ∈ R) : (f : Ω) ^ m * a ∈ R := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hnm
  rw [pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem f.2 j) h

theorem expand {k r : ℕ} (f d : Fin k → R) (B : Fin k → Module.Basis (Fin r) Ω E) (M N : ℕ)
    (hd : ∑ l, d l * f l ^ (M + N) = 1) (e : E) :
    ∑ i : Fin k × Fin r, ((d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2)) •
      ((f i.1 : Ω) ^ N • B i.1 i.2) = e := by
  have hd' : ∑ l, (d l : Ω) * (f l : Ω) ^ (M + N) = 1 := by
    simpa using congrArg Subtype.val hd
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← one_smul Ω e, ← hd', Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← (B l).sum_repr e, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem exists_dualBasis {r : ℕ} {L : Submodule R E} (h : LocFree R r L.toAddSubgroup) :
    ∃ (k : ℕ) (φ : Fin k × Fin r → Module.Dual Ω E) (v : Fin k × Fin r → L),
      (∀ i, ∀ e ∈ L, φ i e ∈ R) ∧ ∀ e, ∑ i, φ i e • (v i : E) = e := by
  classical
  obtain ⟨k, f, c, B, hs, h1, h2⟩ := exists_charts h
  choose n hn using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ l q, n l q ≤ N := by
    obtain ⟨N, hN⟩ := (Set.finite_range fun i : Fin k × Fin r => n i.1 i.2).bddAbove
    exact ⟨N, fun l q => hN ⟨(l, q), rfl⟩⟩
  let v : Fin k × Fin r → L := fun i =>
    ⟨(f i.1 : Ω) ^ N • B i.1 i.2, pow_smul_mem _ (hN _ _) (hn _ _)⟩

  have hspan : ∀ e ∈ L, e ∈ Submodule.span R (Set.range fun i => (v i : E)) := by
    intro e he
    choose m hm using fun l q => h2 l q e he
    obtain ⟨M, hM⟩ := (Set.finite_range fun i : Fin k × Fin r => m i.1 i.2).bddAbove
    obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
    rw [← expand f d B M N hd e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hR : (d i.1 : Ω) * ((f i.1 : Ω) ^ M * (B i.1).repr e i.2) ∈ R :=
      R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨i, rfl⟩) (hm _ _))
    exact Submodule.smul_mem _ (⟨_, hR⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  choose m hm using fun (i j : Fin k × Fin r) => h2 i.1 i.2 (v j) (v j).2
  obtain ⟨M, hM⟩ := (Set.finite_range fun i : (Fin k × Fin r) × (Fin k × Fin r) =>
    m i.1 i.2).bddAbove
  obtain ⟨d, hd⟩ := exists_pow_cover f c hs (M + N)
  refine ⟨k, fun i => ((d i.1 : Ω) * (f i.1 : Ω) ^ M) • (B i.1).coord i.2, v, ?_, ?_⟩
  · intro i e he
    have he' := hspan e he
    clear he
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have := R.mul_mem (d i.1).2 (pow_mul_mem _ (hM ⟨(i, j), rfl⟩) (hm i j))
      simpa [mul_assoc] using this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Subalgebra.smul_def, map_smul]
      exact R.mul_mem a.2 hx
  · intro e
    simpa [mul_assoc, v] using expand f d B M N hd e

section DualBasis

variable {ι : Type*} [Fintype ι] {L : Submodule R E} (φ : ι → Module.Dual Ω E) (v : ι → L)
  (hφ : ∀ i, ∀ e ∈ L, φ i e ∈ R) (hv : ∀ e, ∑ i, φ i e • (v i : E) = e)

include hφ hv

theorem sum_eq (x : L) : ∑ i, (⟨φ i x, hφ i x x.2⟩ : R) • v i = x := by
  apply Subtype.ext
  simpa [Subalgebra.smul_def] using hv x

theorem finite_projective : Module.Finite R L ∧ Module.Projective R L := by
  classical
  let s : L →ₗ[R] (ι → R) :=
    { toFun := fun x i => ⟨φ i x, hφ i x x.2⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp [Subalgebra.smul_def] }
  let p : (ι → R) →ₗ[R] L := Fintype.linearCombination R v
  have hps : p ∘ₗ s = LinearMap.id := by
    ext1 x
    exact sum_eq φ v hφ hv x
  exact ⟨Module.Finite.of_surjective p fun x => ⟨s x, LinearMap.congr_fun hps x⟩,
    Module.Projective.of_split s p hps⟩

theorem isBaseChange : IsBaseChange Ω L.subtype := by
  let g : E →ₗ[Ω] Ω ⊗[R] L := ∑ i, (φ i).smulRight ((1 : Ω) ⊗ₜ[R] v i)
  have hg : ∀ e, g e = ∑ i, φ i e • ((1 : Ω) ⊗ₜ[R] v i) := by
    intro e
    simp [g]
  refine IsBaseChange.of_equiv (LinearEquiv.ofLinear (L.subtype.liftBaseChange Ω) g ?_ ?_) ?_
  · ext1 e
    simp [hg, hv]
  · ext x
    have : g x = (1 : Ω) ⊗ₜ[R] x := by
      rw [hg]
      conv_rhs => rw [← sum_eq φ v hφ hv x, tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_smul]
      rfl
    simpa using this
  · intro x
    simp

end DualBasis

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup →
      Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧
        IsBaseChange Ω L.subtype := by
  intro o Ω _ _ _ R E _ _ r L h
  obtain ⟨k, φ, v, hφ, hv⟩ := exists_dualBasis h
  refine ⟨(finite_projective φ v hφ hv).1, (finite_projective φ v hφ hv).2, ?_,
    isBaseChange φ v hφ hv⟩
  obtain ⟨k, f, c, B, hs, -⟩ := exists_charts h
  rcases k with _ | k
  · simp at hs
  · simpa using Module.finrank_eq_card_basis (B 0)

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemRangeOfIntegralAtHeightOneOver
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_range_of_integral_at_heightOne_over :
    ∀ (B K : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
      [Field K] [Algebra B K] [IsFractionRing B K] (ϖ : B) (x : K), ϖ ≠ 0 →
      (∃ (N : ℕ) (b : B), algebraMap B K b = algebraMap B K ϖ ^ N * x) →
      (∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∈ P →
        ∃ (b c : B), c ∉ P ∧ algebraMap B K b = algebraMap B K c * x) →
      ∃ b : B, algebraMap B K b = x := by
  intro B K _ _ _ _ _ _ _ ϖ x _ hN hP
  obtain ⟨N, b, hb⟩ := hN
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x
    (fun p hp h1 => by
      by_cases hm : ϖ ∈ p
      · obtain ⟨b', c, hc, hbc⟩ := hP p hp h1 hm
        exact ⟨b', c, hc, by rw [hbc, mul_comm]⟩
      · exact ⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProductInequalitiesForceEquality
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s :=
  PositivityTheory.HtPt.Rh.grcount

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuadraticCharacterPrescribedPlaces
section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.HeightOneFrame

theorem integral_of_integral_at_height_one :
    ∀ (A Ω : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field Ω]
      [Algebra A Ω] [IsFractionRing A Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ)
      (b b' : Fin r → E), LinearIndependent Ω b →
      (∀ P : PrimeSpectrum A, P.asIdeal.height = 1 → ∀ i, ∃ (s : A) (c : Fin r → A),
        s ∉ P.asIdeal ∧ algebraMap A Ω s • b' i = ∑ k, algebraMap A Ω (c k) • b k) →
      (∀ i, b' i ∈ Submodule.span Ω (Set.range b)) →
      ∀ i, ∃ c : Fin r → A, b' i = ∑ k, algebraMap A Ω (c k) • b k := by
  intro A Ω _ _ _ _ _ _ _ E _ _ r b b' hb hP hspan i
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp (hspan i)
  have key : ∀ k, x k ∈ Set.range (algebraMap A Ω) := by
    intro k
    refine GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := Ω) (x k) ?_
    intro p hp h1
    obtain ⟨s, c, hs, hc⟩ := hP ⟨p, hp⟩ h1 i
    refine ⟨c k, s, hs, ?_⟩
    have h0 : ∑ j, (algebraMap A Ω s * x j - algebraMap A Ω (c j)) • b j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
      rw [hx, hc, sub_self]
    have h2 := (Fintype.linearIndependent_iff.mp hb) _ h0 k
    have h3 : algebraMap A Ω s * x k = algebraMap A Ω (c k) := sub_eq_zero.mp h2
    rw [← h3, mul_comm]
  choose c hc using key
  refine ⟨c, ?_⟩
  rw [← hx]
  simp only [hc]

end GlobalTheory.CompanionTheory.HeightOneFrame
end

