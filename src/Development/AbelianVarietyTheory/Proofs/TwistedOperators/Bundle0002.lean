module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseSpanTensorOfDenseSubspaces
section
open scoped InnerProductSpace
open Filter Topology

namespace GlobalTheory

theorem dense_span_tensor_of_dense_subspaces {ι : Type} [Fintype ι] {H : ι → Type}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type}
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs)
    (W : ∀ i, Submodule ℂ (H i)) (hu : ∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs))
    (hW : ∀ i, Dense (W i : Set (H i))) :
    Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) :
      Set Hs) := by
  have hnorm : ∀ x y, ‖u y - u x‖ = Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
      - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) := by
    intro x y
    rw [← hu, ← hu, ← hu, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← norm_sub_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hcont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous (fun y : (∀ i, H i) => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
        - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))) := by
      fun_prop
    have key : Tendsto (fun y => ‖u y - u x‖) (𝓝 x) (𝓝 ‖u x - u x‖) := by
      have e : (fun y => ‖u y - u x‖) = fun y => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
          - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) :=
        funext fun y => hnorm x y
      rw [e, hnorm x x]
      exact hc.tendsto x
    simpa using key
  set S := Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i))))
    with hS
  have hpi : Dense (Set.pi Set.univ (fun i => (W i : Set (H i)))) :=
    dense_pi Set.univ (fun i _ => hW i)
  have hsub : Set.range u ⊆ closure (S : Set Hs) := by
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure hcont (hpi x) ?_
    intro y hy
    apply Submodule.subset_span
    exact ⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, rfl⟩
  have hle : Submodule.span ℂ (Set.range u) ≤ S.topologicalClosure := by
    rw [Submodule.span_le, Submodule.topologicalClosure_coe]
    exact hsub
  have h2 : Dense (S.topologicalClosure : Set Hs) := hd.mono hle
  rwa [Submodule.topologicalClosure_coe, dense_closure] at h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DescMk
section
namespace GlobalTheory.QuotientDescentTwistedOperators

open Topology

noncomputable def desc {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : C(G ⧸ Γ, ℂ) where
  toFun := fun q => Quotient.liftOn' q f (by
    intro a b hab
    rw [QuotientAddGroup.leftRel_apply] at hab
    have := hΓ _ hab a
    rw [← this]
    congr 1
    abel)
  continuous_toFun := hf.quotient_liftOn' _

theorem desc_mk {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G)
    (f : G → ℂ) (hf : Continuous f) (hΓ : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (x : G) :
    desc Γ f hf hΓ (QuotientAddGroup.mk x) = f x := rfl

theorem approx : ∀ (G : Type) [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_6 : MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology ↥Γ] (K : Set G), IsCompact K → (∀ (x : G), ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [inst_9 : AddCommGroup A] (χ : A → G → ℂ), (∀ (a : A), Continuous (χ a)) → (∀ (a : A) (x y : G), χ a (x + y) = χ a x * χ a y) → (∀ (a b : A) (x : G), χ (a + b) x = χ a x * χ b x) → (∀ (x : G), χ (0 : A) x = (1 : ℂ)) → (∀ (a : A) (x : G), ‖χ a x‖ = (1 : ℝ)) → (∀ (x : G), (∀ (a : A), χ a x = (1 : ℂ)) ↔ x ∈ Γ) → ∀ (Φ : G → ℂ), Continuous Φ → (∀ γ ∈ Γ, ∀ (x : G), Φ (γ + x) = Φ x) → ∀ (ε : ℝ), (0 : ℝ) < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ (x : G), ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ χ hc hmulx hadd hzero hnorm hker Φ hΦ hΦinv ε hε

  have : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have hU : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      ext q
      refine QuotientAddGroup.induction_on q fun x => ?_
      obtain ⟨γ, hγ, hk⟩ := hcov x
      refine ⟨fun _ => ⟨γ + x, hk, ?_⟩, fun _ => Set.mem_univ _⟩
      rw [QuotientAddGroup.eq]
      have : -(γ + x) + x = -γ := by abel
      rw [this]
      exact Γ.neg_mem hγ
    rw [hU]
    exact hK.image continuous_quot_mk
  have hχ0 : ∀ a, χ a 0 = 1 := fun a => (hker 0).2 Γ.zero_mem a
  have hinv : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hmulx, (hker γ).2 hγ a, one_mul]

  let e : A → C(G ⧸ Γ, ℂ) := fun a => desc Γ (χ a) (hc a) (hinv a)
  have he_apply : ∀ a x, e a (QuotientAddGroup.mk x) = χ a x := fun a x =>
    desc_mk Γ (χ a) (hc a) (hinv a) x
  have he_add : ∀ a b, e (a + b) = e a * e b := by
    intro a b
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.mul_apply, he_apply, he_apply, he_apply, hadd]
  have he_zero : e 0 = 1 := by
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.one_apply, he_apply, hzero]
  have he_star : ∀ a, star (e a) = e (-a) := by
    intro a
    ext q
    refine QuotientAddGroup.induction_on q fun x => ?_
    rw [ContinuousMap.star_apply, he_apply, he_apply]
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hadd, neg_add_cancel, hzero]
    have h2 : χ a x * star (χ a x) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    linear_combination (-(star (χ a x))) * h1 + χ (-a) x * h2

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hone : (1 : C(G ⧸ Γ, ℂ)) ∈ S := he_zero ▸ Submodule.subset_span ⟨0, rfl⟩
  have hmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    have h := Submodule.mul_mem_mul hf hg
    rw [Submodule.span_mul_span] at h
    refine (Submodule.span_le.mpr ?_) h
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a + b, he_add a b⟩
  have hstar : ∀ f ∈ S, star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨-a, (he_star a).symm⟩
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let B : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hmul f g hf hg
      one_mem' := hone
      add_mem' := fun hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem c hone
      star_mem' := fun {f} hf => hstar f hf }

  have hsep : B.SeparatesPoints := by
    intro q₁ q₂
    refine QuotientAddGroup.induction_on q₁ fun x => QuotientAddGroup.induction_on q₂ fun y => ?_
    intro hne
    have hex : ∃ a, χ a x ≠ χ a y := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hne
      rw [QuotientAddGroup.eq]
      refine (hker _).1 fun a => ?_
      rw [hmulx, ← hall a, ← hmulx, neg_add_cancel, hχ0 a]
    obtain ⟨a, ha⟩ := hex
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    rwa [he_apply, he_apply]

  have hB := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hsep
  let Φq : C(G ⧸ Γ, ℂ) := desc Γ Φ hΦ hΦinv
  have hmem : Φq ∈ closure (B : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hB]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨c, hcg⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show g ∈ S from hg)
  refine ⟨c.support, c, fun x => ?_⟩
  have hval : ∑ a ∈ c.support, c a * χ a x = g (QuotientAddGroup.mk x) := by
    rw [← hcg, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ContinuousMap.smul_apply, he_apply, smul_eq_mul]
  rw [hval, ← desc_mk Γ Φ hΦ hΦinv x]
  calc ‖Φq (QuotientAddGroup.mk x) - g (QuotientAddGroup.mk x)‖
      = ‖(Φq - g) (QuotientAddGroup.mk x)‖ := rfl
    _ ≤ ‖Φq - g‖ := ContinuousMap.norm_coe_le_norm _ _
    _ = dist Φq g := (dist_eq_norm _ _).symm
    _ ≤ ε := hdist.le

end GlobalTheory.QuotientDescentTwistedOperators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetComplexification
section
namespace GlobalTheory.PolarU

open Module

theorem det_complexification (E W : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℂ W] (j : E →+ W) (T : E →ₗ[ℝ] E) (S : W →ₗ[ℂ] W)
    (hj : ∀ (t : ℝ) (x : E), j (t • x) = (t : ℂ) • j x)
    (hspan : ∀ w, ∃ a b, w = j a + Complex.I • j b)
    (hinj : ∀ a b, j a + Complex.I • j b = 0 → a = 0 ∧ b = 0)
    (hS : ∀ x, S (j x) = j (T x)) :
    LinearMap.det S = ((LinearMap.det T : ℝ) : ℂ) := by
  classical
  let bE := Module.finBasis ℝ E
  let v : Fin (Module.finrank ℝ E) → W := fun i => j (bE i)

  have hsum : ∀ c : Fin (Module.finrank ℝ E) → ℝ, j (∑ i, c i • bE i) = ∑ i, (c i : ℂ) • v i := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hj (c i) (bE i))

  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : j (∑ k, (g k).re • bE k) + Complex.I • j (∑ k, (g k).im • bE k) = 0 := by
      rw [hsum, hsum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl (fun k _ => ?_)).trans hg
      rw [smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]
    obtain ⟨h1, h2⟩ := hinj _ _ key
    have r1 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).re) h1 i
    have r2 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).im) h2 i
    exact Complex.ext (by simpa using r1) (by simpa using r2)

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    have hmem : ∀ a : E, j a ∈ Submodule.span ℂ (Set.range v) := by
      intro a
      rw [← bE.sum_repr a, hsum]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    intro w _
    obtain ⟨a, b, rfl⟩ := hspan w
    exact Submodule.add_mem _ (hmem a) (Submodule.smul_mem _ _ (hmem b))
  let bW : Basis (Fin (Module.finrank ℝ E)) ℂ W := Basis.mk hli hsp
  have hbW : ∀ i, bW i = v i := fun i => Basis.mk_apply hli hsp i

  have hmat : LinearMap.toMatrix bW bW S = (LinearMap.toMatrix bE bE T).map Complex.ofRealHom := by
    ext i k
    have e : S (bW k) = ∑ l, ((bE.repr (T (bE k)) l : ℝ) : ℂ) • bW l := by
      simp only [hbW]
      rw [← hsum (bE.repr (T (bE k))), bE.sum_repr]
      exact hS (bE k)
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, e, bW.repr_sum_self]
    rfl
  rw [← LinearMap.det_toMatrix bW S, ← LinearMap.det_toMatrix bE T, hmat]
  exact (RingHom.map_det Complex.ofRealHom _).symm

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EichlerTransvectionUnitaryInverseConj
section
open Matrix

namespace GlobalTheory

theorem eichlerTransvection_unitary_inverse_conj :
    ∀ (A : Type) [CommRing A] [StarRing A] [Invertible (2 : A)] (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) (_ : Gᴴ = G) (h : (ι → A) → (ι → A) → A) (_ : ∀ x y, h x y = star y ⬝ᵥ G.mulVec x) (E : (ι → A) → (ι → A) → (ι → A) → (ι → A)) (_ : ∀ w v y, E w v y = y + h y v • w - h y w • v - (⅟(2 : A) * h v v * h y w) • w), (∀ w v, h w w = 0 → h w v = 0 → ∀ x y, h (E w v x) (E w v y) = h x y) ∧ (∀ w v, h w w = 0 → h w v = 0 → ∀ y, E w (-v) (E w v y) = y) ∧ ∀ (g : Matrix ι ι A), (∀ x y, h (g.mulVec x) (g.mulVec y) = h x y) → ∀ w v y, g.mulVec (E w v y) = E (g.mulVec w) (g.mulVec v) (g.mulVec y) := by
  intro A _ _ _ ι _ _ G hG h hh E hE
  have addl : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y; simp only [hh, mulVec_add, dotProduct_add]
  have subl : ∀ x x' y, h (x - x') y = h x y - h x' y := by
    intro x x' y; simp only [hh, mulVec_sub, dotProduct_sub]
  have negl : ∀ x y, h (-x) y = - h x y := by
    intro x y; simp only [hh, mulVec_neg, dotProduct_neg]
  have smull : ∀ (a : A) x y, h (a • x) y = a * h x y := by
    intro a x y; simp only [hh, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have addr : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; simp only [hh, star_add, add_dotProduct]
  have subr : ∀ x y y', h x (y - y') = h x y - h x y' := by
    intro x y y'; simp only [hh, star_sub, sub_dotProduct]
  have negr : ∀ x y, h x (-y) = - h x y := by
    intro x y; simp only [hh, star_neg, neg_dotProduct]
  have smulr : ∀ (a : A) x y, h x (a • y) = star a * h x y := by
    intro a x y; simp only [hh, star_smul, smul_dotProduct, smul_eq_mul]
  have symm : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [hh, hh, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  have s2 : star (⅟(2 : A)) = ⅟(2 : A) := by
    have := congrArg star h2
    rw [star_mul', star_one, star_ofNat] at this
    linear_combination (⅟(2 : A)) * this - (star (⅟(2 : A))) * h2
  refine ⟨?_, ?_, ?_⟩
  · intro w v hww hwv x y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE, hE]
    simp only [addl, subl, smull, addr, subr, smulr, star_mul', symm, s2, hww, hwv, hvw]
    linear_combination (-(h v v * h x w * h w y)) * h2
  · intro w v hww hwv y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE w (-v), hE w v]
    simp only [addl, subl, smull, negl, negr, hww, hwv, hvw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (-(h v v * h y w * w i)) * h2
  · intro g hg w v y
    rw [hE, hE]
    simp only [hg, mulVec_add, mulVec_sub, mulVec_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EndoApplyEq
section
universe u_1 u_2 u_3

namespace GlobalTheory.OrthogonalProjectionOnto

open Module

section

variable {R : Type u_1} [Ring R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
  (M : ι → Type u_3) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem endo_apply_eq (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0)
    (g : (Π i, M i) →ₗ[R] (Π i, M i)) (x : Π i, M i) (i : ι) :
    g x i = g (Pi.single i (x i)) i := by
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · intro j _ hji
    have h0 := h j i hji ((LinearMap.proj i).comp (g.comp (LinearMap.single R M j)))
    exact LinearMap.congr_fun h0 (x j)
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def projOnto (h : ∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0) (i₀ : ι) :
    End (End R (Π i, M i)) (Π i, M i) where
  toFun x := fun i => if i = i₀ then x i else 0
  map_add' x y := by
    funext i
    split_ifs <;> simp_all
  map_smul' g x := by
    funext i
    simp only [RingHom.id_apply, Module.End.smul_def]
    rw [endo_apply_eq M h g x i, endo_apply_eq M h g (fun i => if i = i₀ then x i else 0) i]
    split_ifs with hi
    · rfl
    · simp

end

theorem main : ∀ {R : Type u_1} [inst : Ring R] {ι : Type u_2} [Fintype ι] [inst_2 : DecidableEq ι]
    (M : ι → Type u_3) [inst_3 : (i : ι) → AddCommGroup (M i)] [inst_4 : (i : ι) → Module R (M i)]
    [∀ (i : ι), IsSimpleModule R (M i)],
    (∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = (0 : M i →ₗ[R] M j)) →
    ∀ (i₀ : ι) (s : (i : ι) → Finset (M i)), ∃ (r : R), ∀ (i : ι), ∀ m ∈ s i,
      r • m = if i = i₀ then m else (0 : M i) := by
  intro R _ ι _ _ M _ _ _ h i₀ s
  letI : DecidableEq (Π i, M i) := Classical.decEq _
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := Π i, M i) (projOnto M h i₀)
    (Finset.univ.biUnion fun i => (s i).image (Pi.single i))
  refine ⟨r, fun i m hm => ?_⟩
  have hmem : Pi.single i m ∈ Finset.univ.biUnion fun i => (s i).image (Pi.single (M := M) i) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact ⟨i, m, hm, rfl⟩
  have := congrFun (hr _ hmem) i
  simp only [projOnto, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, Pi.smul_apply] at this
  exact this.symm

end GlobalTheory.OrthogonalProjectionOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowth
section
open scoped InnerProductSpace

namespace GlobalTheory

open Set Filter Topology

theorem vanish_at_one_of_derivs_vanish_of_growth (φ : ℕ → ℝ → ℂ) (a b : ℝ)
    (hd : ∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) (h0 : ∀ k, φ k 0 = 0)
    (hb : ∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) : φ 0 1 = 0 := by
  set M : ℕ → ℝ := fun n => Real.sqrt (b * a ^ n * n.factorial) with hM
  have base : ∀ k t, ‖φ k t‖ ≤ M k := by
    intro k t
    have := Real.abs_le_sqrt (hb k t)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have key : ∀ m k, ∀ t ∈ Icc (0:ℝ) 1, ‖φ k t‖ ≤ M (k + m) * t ^ m / m.factorial := by
    intro m
    induction m with
    | zero => intro k t _; simpa using base k t
    | succ m ih =>
      intro k
      have hB : ∀ x, HasDerivAt (fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
          (M ((k + 1) + m) * x ^ m / m.factorial) x := by
        intro x
        have h1 := ((hasDerivAt_pow (m + 1) x).const_mul (M (k + (m + 1)))).div_const
          ((m + 1).factorial : ℝ)
        refine h1.congr_deriv ?_
        rw [show k + 1 + m = k + (m + 1) by ring]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
        have : (m.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ k)
        (f' := φ (k + 1)) (a := 0) (b := 1)
        (fun x _ => (hd k x).continuousAt.continuousWithinAt)
        (fun x _ => (hd k x).hasDerivWithinAt)
        (B := fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
        (by simp [h0 k]) hB
        (fun x hx => ih (k + 1) x (Ico_subset_Icc_self hx))
      exact this
  have hn : ∀ n : ℕ, ‖φ 0 1‖ ^ 2 ≤ b * (a ^ n / n.factorial) := by
    intro n
    have h := key n 0 1 (by simp)
    simp only [zero_add, one_pow, mul_one] at h
    have hX : 0 ≤ b * a ^ n * n.factorial := le_trans (by positivity) (hb n 1)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_pow, hM, Real.sq_sqrt hX] at h2
    refine h2.trans (le_of_eq ?_)
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : Tendsto (fun n : ℕ => b * (a ^ n / n.factorial)) atTop (𝓝 (b * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop a).const_mul b
  rw [mul_zero] at ht
  have hle : ‖φ 0 1‖ ^ 2 ≤ 0 := ge_of_tendsto' ht hn
  have : ‖φ 0 1‖ = 0 := by nlinarith [norm_nonneg (φ 0 1)]
  exact norm_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariant
section
open MeasureTheory Pointwise

namespace GlobalTheory

theorem eq_zero_of_ae_fundamentalDomain_of_leftInvariant
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by
  set U : Set G := {x | F x ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hF continuous_const
  have hUinv : ∀ g : Γ, g • U = U := by
    intro g
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, hUdef, Set.mem_setOf_eq, Subgroup.smul_def,
      smul_eq_mul]
    rw [hinv _ (Γ.inv_mem g.2)]
  have hU𝓕 : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    simpa [hUdef] using hae
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hU𝓕
  have hUe : U = ∅ := by
    by_contra hne
    exact (hUo.measure_pos μ (Set.nonempty_iff_ne_empty.mpr hne)).ne' hU0
  intro x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsBis
section
namespace GlobalTheory.OneAddPowBoundTwistedOperators

theorem one_add_pow_le : ∀ {L : ℝ}, (0 : ℝ) ≤ L → ∀ (N : ℕ), ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + L ^ N) := by
  intro L hL N
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hLN : (0 : ℝ) ≤ L ^ N := pow_nonneg hL N
  rcases le_total L 1 with h | h
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    nlinarith
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    nlinarith

end GlobalTheory.OneAddPowBoundTwistedOperators
end

