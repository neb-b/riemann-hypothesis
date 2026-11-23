module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropTerm
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapCEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (i : ℕ) : Cochain G i ≃ₗ[R] Cochain G' i :=
  LinearEquiv.piCongrRight fun I : Idx U i => e I.1

theorem mapCEquiv_d (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : mapCEquiv e (i + 1) (d G ρ i s) = d G' ρ' i (mapCEquiv e i s) :=
  mapC_d (fun I => (e I).toLinearMap) he i s

theorem mem_bdry_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ bdry G ρ i ↔ mapCEquiv e i s ∈ bdry G' ρ' i := by
  cases i with
  | zero =>
    change s ∈ (⊥ : Submodule R _) ↔ mapCEquiv e 0 s ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  | succ i =>
    change s ∈ LinearMap.range (d G ρ i) ↔ mapCEquiv e (i + 1) s ∈ LinearMap.range (d G' ρ' i)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨mapCEquiv e i t, (mapCEquiv_d e he i t).symm⟩
    · rintro ⟨t', ht'⟩
      refine ⟨(mapCEquiv e i).symm t', (mapCEquiv e (i + 1)).injective ?_⟩
      rw [mapCEquiv_d e he, LinearEquiv.apply_symm_apply, ht']

theorem mem_ker_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ LinearMap.ker (d G ρ i) ↔ mapCEquiv e i s ∈ LinearMap.ker (d G' ρ' i) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← mapCEquiv_d e he, LinearEquiv.map_eq_zero_iff]

def kerEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G' ρ' i) :=
  LinearEquiv.ofSubmodules (mapCEquiv e i) _ _ (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_iff e he,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

def equivH (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  Submodule.Quotient.equiv _ _ (kerEquiv e he i) (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, mem_bdry_iff e he]
    congr! 1
    change mapCEquiv e i ((mapCEquiv e i).symm (z : Cochain G' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

end Cech

section Mul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

def mulSubMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) (I : Chart x) : F₁.sub I →ₗ[k] G₁.sub I where
  toFun y := ⟨s * y, h₁ I y y.2⟩
  map_add' a b := Subtype.ext (mul_add s (a : Ω) b)
  map_smul' c y := Subtype.ext (by
    change s * ((c • y : F₁.sub I) : Ω) = ((c • (⟨s * y, h₁ I y y.2⟩ : G₁.sub I) : G₁.sub I) : Ω)
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, mul_smul_comm])

def mulQuotMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mapQ (SubSystem.quotSub G₁ G₂ I) (mulSubMap h₁ I)
    (fun y hy => (h₃ I y y.2).mpr hy)

theorem mulQuotMap_bijective (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz

end Mul

theorem MulQuotEq.proof : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionNonvanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem SectionNonvanish.proof : SectionNonvanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp _ hle ⟨i, hi⟩ D hD
  have hxi : x i ≠ 0 := fun h0 =>
    hi (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i)).mpr (by rw [aeval_X, h0])))
  refine not_forall_not.mp fun hcon => ?_
  let I : Chart x := singleChart hxi
  have hsec : ∀ s ∈ D.toSubSystem.secs, s ∈ idealMod pp I * D.toSubSystem.sub I := by
    intro s hs
    by_contra hs'
    refine hcon s ⟨hs, I, ?_⟩
    rwa [SubSystem.twist_sub_eq_mul_of_line]
  obtain ⟨P, hP⟩ := D.invertible I
  have hsub : D.toSubSystem.sub I ≤ idealMod pp I * D.toSubSystem.sub I := by
    rw [← hD I, Submodule.span_le]
    intro s hs
    rw [hD I]
    exact hsec s hs
  have hone : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I :=
    calc (1 : Submodule (chartRing k x I) Ω) = D.toSubSystem.sub I * P := hP.symm
      _ ≤ idealMod pp I * D.toSubSystem.sub I * P := mul_le_mul' hsub le_rfl
      _ = idealMod pp I := by rw [mul_assoc]; erw [hP]; rw [mul_one]
  have h1 : (1 : Ω) ∈ idealMod pp I := hone (Submodule.mem_one.mpr ⟨1, map_one _⟩)
  refine SectionCount.Drop.Term.one_not_mem_idealMod hpp hle (I := I) (fun j hj => ?_) h1
  obtain rfl : j = i := Finset.mem_singleton.mp hj
  exact hi

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem eulerCharQuot_self {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubSystem k x E) : eulerCharQuot k F F = 0 := by
  unfold eulerCharQuot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  have h2 : Subsingleton (Cech.Cochain (fun I => F.sub I ⧸ SubSystem.quotSub F F I) i) := by
    unfold Cech.Cochain; infer_instance
  have h3 : Subsingleton (SubSystem.quotH F F i) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  simp [Module.finrank_zero_of_subsingleton]

theorem subSystem_ext {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    {F G : SubSystem k x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by
  obtain ⟨sF, mF⟩ := F
  obtain ⟨sG, mG⟩ := G
  have : sF = sG := funext h
  subst this
  rfl

theorem twist_idealSys_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by
  refine subSystem_ext fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
      isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
  have hle : (idealSys x pp).sub I ≤ 1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
    exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine le_antisymm (Submodule.mul_le.mpr fun q hq y hy => ?_) fun y hy => by
    simpa using Submodule.mul_mem_mul h1 hy
  obtain ⟨q', rfl⟩ := Submodule.mem_one.mp (hle hq)
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ q' hy

theorem pieceChar_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by
  unfold pieceChar
  rw [twist_idealSys_of_irrelevant pp hpp a]
  exact eulerCharQuot_self _

end Lemmas

section Dim

variable {R : Type*} [CommRing R]

theorem ringKrullDim_quotient_succ_le_of_lt {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by
  obtain ⟨r, hrq, hrp⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk pp r ∈ nonZeroDivisors (R ⧸ pp) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk pp r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hrq, mul_zero]
  have := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hker (Ideal.Quotient.factor_surjective h.le))
  gcongr

end Dim

section Induction

variable {k : Type u} [Field k] {N : ℕ}

theorem one_le_ringKrullDim_of_relevant (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by
  obtain ⟨i, hi⟩ := hrel
  have hle : pp ≤ RingHom.ker (constantCoeff : Poly k N →+* k) := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h0
    have h1 := hh f hf 0
    rw [homogeneousComponent_zero] at h1
    have h0' : AddMonoidAlgebra.coeff f 0 ≠ 0 := by rwa [← constantCoeff_eq]
    have hu : IsUnit (C (AddMonoidAlgebra.coeff f 0) : Poly k N) := (isUnit_iff_ne_zero.mpr h0').map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  have hlt : pp < RingHom.ker (constantCoeff : Poly k N →+* k) :=
    lt_of_le_of_ne hle fun h => hi (h ▸ by simp [RingHom.mem_ker])
  have hnt : Nontrivial (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
    _ ≤ ringKrullDim (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) + 1 :=
        by gcongr; exact ringKrullDim_nonneg_of_nontrivial
    _ ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_quotient_succ_le_of_lt hlt

theorem withBot_le_of_succ_le {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + 1 ≤ (D : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

theorem isNumPolyLT_sum {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by
  choose Q hQ hev using h
  refine ⟨∑ m, Q m, ?_, fun n c => by simp [hev, map_sum]⟩
  rcases Nat.eq_zero_or_pos D with hD | hD
  · left
    subst hD
    exact Finset.sum_eq_zero fun m _ => (hQ m).resolve_right (Nat.not_lt_zero _)
  · right
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hD)]
    intro m _
    rcases hQ m with h0 | h0
    · rw [h0, totalDegree_zero]; exact hD
    · exact h0

theorem IsNumPolyLT.congr {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by
  obtain ⟨Q, hQ, hev⟩ := h
  exact ⟨Q, hQ, fun n c => (hfg n c).symm.trans (hev n c)⟩

variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}

theorem pieceChar_isNumPolyLT (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by
  induction D with
  | zero =>
    intro pp hp hh _ hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have := (one_le_ringKrullDim_of_relevant pp hh hrel).trans hdim
      exact absurd this (by simp)
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
  | succ D ih =>
    intro pp hp hh hle hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have key : ∀ (qq : Ideal (Poly k N)) (b : ℤ), qq.IsPrime →
          (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) → pp < qq →
          IsNumPolyLT t D (fun n c => (pieceChar k qq b L n c : ℚ)) := fun qq b hq hqh hlt =>
        ih qq hq hqh (hle.trans hlt.le)
          (withBot_le_of_succ_le ((ringKrullDim_quotient_succ_le_of_lt hlt).trans hdim)) b
      obtain ⟨i, hi⟩ := hrel
      obtain ⟨r, qq, b, hqq, heq⟩ := hH k Ω N x pp hp hh hle i hi a
      have h0 : IsNumPolyLT t D
          (fun n c => (pieceChar k pp a L n (c + 1) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        (isNumPolyLT_sum _ fun m => key (qq m) (b m) (hqq m).1 (hqq m).2.1
          (lt_of_le_of_ne (hqq m).2.2.1 fun h => hi (h ▸ (hqq m).2.2.2))).congr
          fun n c => by exact_mod_cast (heq t L n c).symm
      choose μ r' qq' b' hqq' heq' using fun j => hS k Ω N x pp hp hh hle ⟨i, hi⟩ t L j a
      have hj : ∀ j, IsNumPolyLT t D (fun n c =>
          (pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ j) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        fun j => (isNumPolyLT_sum _ fun m => key (qq' j m) (b' j m) (hqq' j m).1 (hqq' j m).2.1
          (hqq' j m).2.2).congr fun n c => by exact_mod_cast (heq' j n c).symm
      exact hP t D (fun n c => (pieceChar k pp a L n c : ℚ)) μ h0 hj
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩

end Induction

theorem Snapper.proof (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x e hZ E _ _ _ _ F hF t L
  obtain ⟨r, pp, a, hpp, heq⟩ := hD k Ω N x E F hF
  have hdim : ∀ m, ringKrullDim (Poly k N ⧸ pp m) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := fun m =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (hpp m).2.2)).trans hZ.dim.le
  obtain ⟨Q, hQ, hev⟩ := isNumPolyLT_sum (fun m n c => (pieceChar k (pp m) (a m) L n c : ℚ))
    fun m => pieceChar_isNumPolyLT hH hS hP L (e + 1) (pp m) (hpp m).1 (hpp m).2.1 (hpp m).2.2 (hdim m) (a m)
  refine ⟨Q, ?_, fun n c => ?_⟩
  · rcases hQ with h0 | h0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  · rw [heq t L n c, ← hev n c]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnW
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem StepThree.OnW.proof (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.OnW.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  obtain ⟨c₁, h₁⟩ := hL k Ω N x T hK pp hpp
  obtain ⟨c₂, h₂⟩ := hG k Ω N x T hK pp hpp
  refine ⟨max c₁ c₂, fun b c hb hc I => ?_⟩
  refine (h₂ b c hb (le_of_max_le_right hc) I).trans (sup_le ?_ le_sup_right)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, hcomp, rfl⟩
  obtain ⟨t, ht, hts⟩ := h₁ b c hb (le_of_max_le_left hc) s hs hcomp
  have he : s I = t - (t - s I) := by abel
  rw [SetLike.mem_coe, he]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span (SetLike.mem_coe.mpr ht)))
    (Submodule.mem_sup_right (hts I))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

