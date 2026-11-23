module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace CechDSq

variable {n : ℕ}

theorem sgn_mul_sgn_of_lt {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  have h1 : (K.erase k).filter (· < j) = K.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzj⟩; exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩; exact ⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩
  have h3 : j ∈ K.filter (· < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold Cech.sgn
  rw [h1, ← h2, pow_succ]
  ring

theorem sgn_mul_sgn_swap {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sgn_mul_sgn_of_lt hj h
  · rw [sgn_mul_sgn_of_lt hk h, neg_neg]

variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}


open Classical in
def restrictTo {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (A : Finset (Fin n)) : G K :=
  if h : ∃ L : Cech.Idx U i, L.1.1 = A ∧ A ⊆ K.1 then
    ρ h.choose.1 K (by rw [h.choose_spec.1]; exact h.choose_spec.2) (s h.choose)
  else 0

theorem restrictTo_eq {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by
  have hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1 := ⟨L, rfl, h⟩
  have key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1),
      ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂) := by
    rintro _ _ rfl _ _; rfl
  rw [restrictTo, dite_eq_left hex]
  exact key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _

end CechDSq


open CechDSq in
theorem CechDSq.proof : CechDSq.Statement := by
  intro n U R _ G _ _ ρ hρ i s
  classical
  funext K
  have hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I),
      ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x := fun I J L h₁ h₂ x =>
    LinearMap.congr_fun (hρ I J L h₁ h₂) x

  let f : (Σ _ : Fin n, Fin n) → G K.1 := fun p =>
    (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) •
      restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)
  have step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k)
      (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩ := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cech.d_apply, map_sum, Finset.smul_sum]
    refine Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, hcomp, ← restrictTo_eq]
    rfl
  show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0
  rw [Cech.d_apply, Finset.sum_congr rfl fun k _ => step k,
    Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩),
    Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [f]
    rw [Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]
  · rintro ⟨k, j⟩ hp - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩
  · rintro ⟨k, j⟩ -
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open TensorProduct MvPolynomial

noncomputable section

universe u v

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']

variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']

variable [Module.Flat S S']

end FlatBC

namespace FlatBC

section Hom

variable {R : Type*} [CommRing R] {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [AddCommGroup Z] [Module R Z]

end Hom

end FlatBC

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S']
variable {X Y Z X' Y' Z' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup Z] [Module S Z] [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']
  [AddCommGroup Z'] [Module S' Z']

end FlatBC

namespace FlatBC

section CechDeg

open Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R] {G : Cell U → Type*}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

end CechDeg

section Poly

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] (N : ℕ)

variable {S S' N}

end Poly

end FlatBC

namespace FlatBC

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

variable {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)



end Loc

end FlatBC

namespace FlatBC

section Grade

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c)




end Grade

end FlatBC

namespace FlatBC

section Final

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S'] [Module.Flat S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c) (c : ℤ)

end Final

end FlatBC

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

theorem CechTop.proof : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem Generated.proof (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      refine Submodule.span_induction
        (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)
      · rintro _ ⟨j, f, e', hf, hee, rfl⟩
        rw [smul_eq_mul, smul_eq_mul]
        exact hgenT j f s e e' hs hf hse (by omega)
      · rw [smul_zero, mul_zero]; exact T.zero_mem
      · intro m m' _ _ h h'
        rw [smul_add, mul_add]; exact T.add_mem h h'
      · intro r m _ h
        have : x i ^ c * ((aeval x s)⁻¹ • (r • m)) =
            (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m)) := by
          rw [chartRing_smul_def]
          simp only [smul_eq_mul, Algebra.smul_def]
          change _ = algebraMap S Ω r * _
          ring
        rw [this]; exact T.smul_mem _ h
    · rw [mul_zero]; exact T.zero_mem
    · intro y y' _ _ h h'
      rw [mul_add]; exact T.add_mem h h'
    · intro b y _ h
      have : x i ^ c * (b • y) = b • (x i ^ c * y) := by
        rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem b h
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreTail.proof (hFin : SerreFinite.Statement.{u, v}) (hOnto : SerreOnto.Statement.{u, v}) :
    SerreTail.Statement.{u, v} := by
  classical
  intro S _ _ N M _ _ _ _ 𝓜 hM c₁

  have hfg : ∀ c : ℤ, ∃ s : Finset (Cech.Cochain (locSys S N M) 0),
      Submodule.span S (s : Set _) = Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 := by
    intro c
    have h0 : (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
        (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype = ⊥ := by
      change Submodule.comap _ ⊥ = ⊥
      rw [Submodule.comap_bot, Submodule.ker_subtype]
    have hf : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0 ⧸
        (Cech.bdryDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).comap
          (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0).subtype) := hFin S N M 𝓜 hM 0 c
    have hf' : Module.Finite S (Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS 0) :=
      Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)
    obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hf'
    exact ⟨s, hs⟩
  choose s hs using hfg
  obtain ⟨c₀, hc₀⟩ := hOnto S N M 𝓜 hM
  set c₂ := max c₀ c₁

  let Φ : M →ₗ[Poly S N] Cech.Cochain (locSys S N M) 0 := LinearMap.pi fun I => locMk M I.1.1
  let T : Finset (Cech.Cochain (locSys S N M) 0) := (Finset.Ico c₁ c₂).biUnion s
  let B : Submodule (Poly S N) (Cech.Cochain (locSys S N M) 0) :=
    LinearMap.range Φ ⊔ Submodule.span (Poly S N) (T : Set _)
  have hB : B.FG := by
    refine Submodule.FG.sup ?_ (Submodule.fg_span T.finite_toSet)
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map Φ

  have hA : H0tail 𝓜 c₁ ≤ B.restrictScalars S := by
    refine iSup₂_le fun c hc => ?_
    intro z hz
    by_cases hc2 : c₂ ≤ c
    · obtain ⟨m, hm⟩ := hc₀ c (le_trans (le_max_left _ _) hc2) (Submodule.Quotient.mk ⟨z, hz⟩)
      have hz' : (constCochain (m : M) : Cech.Cochain (locSys S N M) 0) = z := by
        have := (Submodule.Quotient.eq _).mp hm
        change _ ∈ Submodule.comap _ ⊥ at this
        rw [Submodule.mem_comap, Submodule.mem_bot, map_sub, sub_eq_zero] at this
        exact this
      rw [← hz']
      exact Submodule.mem_sup_left ⟨(m : M), rfl⟩
    · have hcI : c ∈ Finset.Ico c₁ c₂ := Finset.mem_Ico.mpr ⟨hc, lt_of_not_ge hc2⟩
      rw [← hs c] at hz
      refine Submodule.mem_sup_right (Submodule.span_le_restrictScalars S (Poly S N) _ ?_)
      refine Submodule.span_mono ?_ hz
      intro y hy
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨c, hcI, hy⟩)
  have hspan : Submodule.span (Poly S N) (H0tail 𝓜 c₁ : Set (Cech.Cochain (locSys S N M) 0)) ≤ B :=
    Submodule.span_le.mpr hA
  have : IsNoetherian (Poly S N) B := isNoetherian_of_fg_of_noetherian B hB
  obtain ⟨t, ht, hteq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp
    (Submodule.FG.of_le_of_isNoetherian hspan)
  refine ⟨t, fun z hz => ht hz, fun z hz => ?_⟩
  change z ∈ Submodule.span (Poly S N) (t : Set _)
  rw [← hteq]
  exact Submodule.subset_span hz

end

end GroundTheory.Heights₂.Heights.Kleiman
end

