module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSimplexFacePairsAcyclicPositiveDegree
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.PrAcyc

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨(Fin.cons (0 : Fin (N + 1)) fun k : Fin (p + 1) => a.toOrderHom k : Fin (p + 2) → Fin (N + 1)),
    by
      intro x y hxy
      induction x using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ x =>
        induction y using Fin.cases with
        | zero => exact absurd hxy (by simp [Fin.le_def])
        | succ y =>
          simp only [Fin.cons_succ]
          exact a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 hxy)⟩

theorem cone_succ {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (k : Fin (p + 1)) :
    (cone a).toOrderHom k.succ = a.toOrderHom k := rfl

theorem δ_zero_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext k
  simp [SimplexCategory.δ, cone_succ]

theorem δ_succ_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k => ?_))
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    show (cone a).toOrderHom (i.succ.succAbove k.succ) = (cone (SimplexCategory.δ i ≫ a)).toOrderHom k.succ
    rw [Fin.succ_succAbove_succ, cone_succ, cone_succ]
    rfl

abbrev v0 (N : ℕ) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N := SimplexCategory.const _ _ 0

theorem δ_one_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 N := by
  ext k
  fin_cases k
  rfl

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) 1 := by
  show ∑ i : Fin (p + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) 1 := by
  show ∑ j : Fin (r + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem d₁_cone_succ {N q r : ℕ} (a : SimplexCategory.mk (q + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨q + 1 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨q + 1, r, a, b⟩ : Pr N) 1 -
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

theorem d₁_cone_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨0, r, a, b⟩ : Pr N) 1 - Finsupp.single (⟨0, r, v0 N, b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_two, δ_zero_cone, δ_one_cone]
  simp [sub_eq_add_neg]

theorem d₂_cone_succ {N p s : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (s + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, s + 1 + 1, a, cone b⟩ : Pr N) = Finsupp.single (⟨p, s + 1, a, b⟩ : Pr N) 1 -
      ∑ j : Fin (s + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, s + 1, a, cone (SimplexCategory.δ j ≫ b)⟩ : Pr N) 1 := by
  rw [d₂_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

def hz {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨z.1 + 1, z.2.1, cone z.2.2.1, z.2.2.2⟩ : Pr N) 1 +
    if z.1 = 0 then Finsupp.single (⟨0, z.2.1 + 1, v0 N, cone z.2.2.2⟩ : Pr N) 1 else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ hz

theorem H_single {N : ℕ} (z : Pr N) : H N (Finsupp.single z 1) = hz z := by
  simp [H, Finsupp.linearCombination_single]

theorem d_single {N : ℕ} (z : Pr N) : Pr.d N (Finsupp.single z 1) = z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂ := by
  simp [Pr.d, Finsupp.linearCombination_single]

theorem H_sum {N n : ℕ} (f : Fin n → Pr N) :
    H N (∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (f i) 1) = ∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • hz (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, H_single]

theorem key {N : ℕ} (z : Pr N) (hpos : 0 < z.1 + z.2.1) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  rcases z with ⟨p, r, a, b⟩
  rw [H_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp at hpos
    | succ s =>
      simp only [hz, if_pos rfl, if_true, map_add (f := _), d_single]
      rw [d₁_cone_zero, d₂_succ, d₁_zero, d₂_cone_succ, d₁_zero, d₂_succ, map_zero, map_smul, H_sum]
      simp only [hz, if_true, ↓reduceIte, Finset.sum_add_distrib, smul_add]
      module
  | succ q =>
    simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero, map_add (f := _), d_single, map_smul]
    rw [d₁_cone_succ, d₁_succ, H_sum]
    have hX : ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • hz (⟨q, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) =
        ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
      simp only [hz, smul_add, Finset.sum_add_distrib]
      rcases q with _ | t
      · simp [Fin.sum_univ_two]
      · simp
    rw [hX]
    cases r with
    | zero => rw [d₂_zero, d₂_zero, map_zero]; module
    | succ s =>
      rw [d₂_succ, d₂_succ, H_sum]
      simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero]
      rw [pow_succ]
      module

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem hz_deg {N : ℕ} (w z : Pr N) (h : z ∈ (hz w).support) : z.1 + z.2.1 = w.1 + w.2.1 + 1 := by
  rcases w with ⟨p, r, a, b⟩
  have h' := Finsupp.support_add h
  rcases Finset.mem_union.1 h' with h1 | h1
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
    split_ifs at h1 with he
    · subst he; simp; omega
    · simp at h1
  · split_ifs at h1 with hp
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
      split_ifs at h1 with he
      · subst he; simp at hp ⊢; omega
      · simp at h1
    · simp at h1

theorem deg_H {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz'
  rw [H, Finsupp.linearCombination_apply] at hz'
  obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hz')
  have := hz_deg w z (Finsupp.support_smul hzw)
  rw [this, hc w hw]

theorem homotopy {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) :
    Pr.d N (H N c) + H N (Pr.d N c) = c := by
  have step : ∀ z ∈ c.support, Pr.d N (H N (Finsupp.single z (c z))) + H N (Pr.d N (Finsupp.single z (c z))) =
      Finsupp.single z (c z) := by
    intro z hz'
    have := key z (by rw [hc z hz']; omega)
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, this]
  calc Pr.d N (H N c) + H N (Pr.d N c)
      = Pr.d N (H N (c.sum Finsupp.single)) + H N (Pr.d N (c.sum Finsupp.single)) := by rw [Finsupp.sum_single]
    _ = ∑ z ∈ c.support, Finsupp.single z (c z) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl step
    _ = c := Finsupp.sum_single c

theorem pr_acyclic : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  intro N k c hc hd
  refine ⟨H N c, deg_H c hc, ?_⟩
  have := homotopy c hc
  rwa [hd, map_zero, add_zero] at this

end GlobalTheory.PrAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleHypercohomologyOfRetract
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RetractAcyc

def resMapRetractHomotopy (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M) :
    Homotopy (resMap R i ≫ resMap R r) (𝟙 (res R M)) := by
  have H : Homotopy (InjectiveResolution.desc i (injectiveResolution M') (injectiveResolution M) ≫
      InjectiveResolution.desc r (injectiveResolution M) (injectiveResolution M'))
      (𝟙 (injectiveResolution M).cocomplex) :=
    (InjectiveResolution.descCompHomotopy i r _ _ _).symm.trans
      (by rw [h]; exact InjectiveResolution.descIdHomotopy _ _)
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] at H2
  exact H2

theorem post_post_of_retract (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M)
    (K : Cx R) (n : ℤ) (x : HK R K M n) : HK.post R K r n (HK.post R K i n x) = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have Hh := resMapRetractHomotopy R i r h
  change CohomologyClass.mk (zcomp (zcomp α (Cocycle.ofHom (resMap R i)) (add_zero n))
    (Cocycle.ofHom (resMap R r)) (add_zero n)) = CohomologyClass.mk α
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy Hh) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
  ext p q hpq
  simp [zcomp, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]

theorem subsingleton_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M →
    ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  intro R _ M M' i r h K n hs
  exact (Function.LeftInverse.injective (g := HK.post R K r n) (f := HK.post R K i n)
    (post_post_of_retract R i r h K n)).subsingleton

end GlobalTheory.EtC.RetractAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModulo
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.PicLoc

open Algebra in
theorem finite_maximalSpectrum_of_field (B : Type) [CommRing B] (S : Submonoid B) (K : Type)
    [Field K] [Algebra B K] [IsLocalization S K] (A' : Type) [CommRing A'] [Algebra B A']
    [FormallyUnramified B A'] [FiniteType B A'] (R : Type) [CommRing R] [Algebra A' R]
    [IsLocalization (algebraMapSubmonoid A' S) R] [Algebra B R] [IsScalarTower B A' R] :
    Finite (MaximalSpectrum R) := by
  letI : Algebra K R := localizationAlgebra S A'
  haveI : IsScalarTower B K R := isScalarTower_localizationAlgebra S A'
  haveI : FormallyEtale A' R := FormallyEtale.of_isLocalization (algebraMapSubmonoid A' S)
  haveI : FormallyUnramified B R := FormallyUnramified.comp B A' R
  haveI : FormallyUnramified K R := FormallyUnramified.of_restrictScalars B K R
  haveI : EssFiniteType A' R := EssFiniteType.of_isLocalization R (algebraMapSubmonoid A' S)
  haveI : EssFiniteType B R := EssFiniteType.comp B A' R
  haveI : EssFiniteType K R := EssFiniteType.of_comp B K R
  haveI : Module.Finite K R := FormallyUnramified.finite_of_free K R
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  infer_instance

theorem isField_localization (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (h0 : (0 : B) ∉ (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f) :
    IsField (Localization ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)) := by
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  haveI : IsDomain (Localization S) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors h0)

  have hbot : ∀ Q : Ideal (Localization S), Q.IsPrime → Q = ⊥ := by
    intro Q hQ
    set p := Q.comap (algebraMap B (Localization S)) with hp
    haveI : p.IsPrime := Ideal.comap_isPrime _ Q
    have hdisj : ∀ s ∈ S, s ∉ p := by
      intro s hs hsp
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp
        (IsLocalization.map_units (Localization S) ⟨s, hs⟩))
    have hp0 : p = ⊥ := by
      by_contra hne
      have hmax : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
      have hf : f ∉ p := fun h => hdisj f (Submonoid.mem_sup_right (Submonoid.mem_powers f)) h
      have htop : p ⊔ Ideal.span {f} = ⊤ := by
        refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hf ?_)
        rw [h]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : B) ∈ p ⊔ Ideal.span {f})
      have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
        have hb0 : Ideal.Quotient.mk (Ideal.span {f}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
        have : Ideal.Quotient.mk (Ideal.span {f}) a = 1 := by
          rw [← map_one (Ideal.Quotient.mk (Ideal.span {f})), ← hab, map_add (f := _), hb0, add_zero]
        rw [this]; exact isUnit_one
      exact hdisj a (Submonoid.mem_sup_left hunit) ha
    rw [← IsLocalization.map_under S (Localization S) Q]
    change Ideal.map _ p = ⊥
    rw [hp0, Ideal.map_bot]
  haveI : Ring.KrullDimLE 0 (Localization S) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (⊥ : Ideal (Localization S)) bot_ne_top
    rw [hbot I hI, ← hbot m hm.isPrime]
    exact hm
  exact Ring.KrullDimLE.isField_of_isDomain

end GlobalTheory.PicLoc

namespace GlobalTheory.PicLoc

theorem subsingleton_pic_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  intro B _ _ f A' _ _ _
  set S : Submonoid B := (IsUnit.submonoid (B ⧸ Ideal.span {f})).comap
      (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f with hS
  suffices Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) from
    inferInstance
  by_cases h0 : (0 : B) ∈ S
  · have h0' : (0 : A') ∈ Algebra.algebraMapSubmonoid A' S :=
      Submonoid.mem_map.2 ⟨0, h0, map_zero _⟩
    letI := IsLocalization.uniqueOfZeroMem
      (S := Localization (Algebra.algebraMapSubmonoid A' S)) h0'
    haveI : IsEmpty (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid A' S))) :=
      ⟨fun m => m.isMaximal.ne_top (by
        rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Localization _) 0]
        exact m.asIdeal.zero_mem)⟩
    infer_instance
  · letI : Field (Localization S) := (isField_localization B f h0).toField
    exact finite_maximalSpectrum_of_field B S (Localization S) A'
      (Localization (Algebra.algebraMapSubmonoid A' S))

end GlobalTheory.PicLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
section
set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory.Nef

def symMat {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun a i => ((C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a

theorem symMat_mulVec {R : Type} [CommRing R] (m : ℕ) (A : Matrix (Fin 2) (Fin 2) R)
    (p : Fin (m + 1) → R) :
    (symMat m A).mulVec p = fun a =>
      (∑ i : Fin (m + 1), C (p i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i)).coeff a := by
  funext a
  simp only [Matrix.mulVec, dotProduct, symMat, Matrix.of_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, coeff_C_mul, mul_comm]

theorem symMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) : (symMat m A).map f = symMat m (A.map f) := by
  ext a i
  simp only [symMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map]
  simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add (f := _)]

def twistAt {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : Place k F → Matrix (Fin n) (Fin n) F := by
  classical
  exact fun v => if v = v₀ then c • h v else h v

theorem twistAt_self {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) : twistAt v₀ c h v₀ = c • h v₀ := by
  simp [twistAt]

theorem twistAt_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (v : Place k F) (hv : v ≠ v₀) :
    twistAt v₀ c h v = h v := by
  simp [twistAt, hv]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLatIsOpenIsCompact
section
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ball_eq_image {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp (-k)} = (fun x => ϖ ^ k * x) '' {x : L | Valued.v x ≤ 1} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hk : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩
    show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hk]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)
    rw [map_mul, hk]
    exact (mul_le_mul' le_rfl hy).trans (by rw [mul_one])

theorem isOpen_vball {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)

theorem isCompact_vball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)

end GlobalTheory.BorelUMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPointStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_baseChange_transport_point : ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (exact GlobalTheory.KeyOriginCut.torsor_baseChange_point) | (intros; apply GlobalTheory.KeyOriginCut.torsor_baseChange_point  <;> assumption)
end

