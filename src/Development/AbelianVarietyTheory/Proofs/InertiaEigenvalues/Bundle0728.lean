module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalAtNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.GlueSpan

theorem glue_rules {K : Type} [Field K] {ι : Type} [Fintype ι]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
    (ea eb : ι → ℕ) {N : ℕ} (t g : Fin N → Rules pts)
    (ht : ∀ i, t i ∈ secW pts mapR borR eb)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    (hg : ∀ i, g i ∈ secW pts mapR borR (ea + eb)) (hc : ∀ i i', g i * t i' = g i' * t i) :
    ∃ h ∈ secW pts mapR borR ea, ∀ i, h * t i = g i := by
  classical
  have hs0 : ∀ (p : TRing K) (y : pts p.R), ∃ s : Fin N → p.R, ∑ i, s i * t i p y = 1 := by
    intro p y
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      ((hunit p y).symm ▸ Submodule.mem_top (x := (1 : p.R)))
    exact ⟨s, by simpa [smul_eq_mul] using hs⟩
  choose s hs using hs0
  have hc' : ∀ (p : TRing K) (y : pts p.R) i i', g i p y * t i' p y = g i' p y * t i p y :=
    fun p y i i' => congrFun (congrFun (hc i i') p) y
  have indep : ∀ (p : TRing K) (y : pts p.R) (s' : Fin N → p.R), ∑ i, s' i * t i p y = 1 →
      ∑ i, s' i * g i p y = ∑ i, s p y i * g i p y := by
    intro p y s' h'
    calc ∑ i, s' i * g i p y = (∑ i, s' i * g i p y) * (∑ i', s p y i' * t i' p y) := by rw [hs, mul_one]
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i p y * t i' p y) := by
          rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i, ∑ i', s' i * s p y i' * (g i' p y * t i p y) := by simp_rw [hc']
      _ = (∑ i', s p y i' * g i' p y) * (∑ i, s' i * t i p y) := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]; refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, s p y i * g i p y := by rw [h', mul_one]
  let h : Rules pts := fun p y => ∑ i, s p y i * g i p y
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro p q φ y z hyz
    have e1 : ∑ i, φ (s p y i) * t i q z = 1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [(ht _).1 p q φ y z hyz, ← map_mul, ← map_sum, hs, map_one]
    show ∑ i, s q z i * g i q z = φ (∑ i, s p y i * g i p y)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← indep q z _ e1, map_sum]
    simp_rw [(hg _).1 p q φ y z hyz, map_mul]
  · intro p u y y' hyy
    have hw : ∀ e : ι → ℕ, wchar e u = ((∏ i, u i ^ e i : (p.R)ˣ) : p.R) := by
      intro e; simp [wchar, Units.coe_prod]
    have hadd : wchar (ea + eb) u = wchar ea u * wchar eb u := by
      simp only [wchar, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    set v : (p.R)ˣ := ∏ i, u i ^ eb i with hv
    have e1 : ∑ i, (s p y i * ((v⁻¹ : (p.R)ˣ) : p.R)) * t i p y' = 1 := by
      simp_rw [(ht _).2 p u y y' hyy, hw eb, ← hv]
      rw [← hs p y]; refine Finset.sum_congr rfl fun i _ => ?_
      calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * ((v : p.R) * t i p y)
          = s p y i * t i p y * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
        _ = s p y i * t i p y := by rw [Units.inv_mul, mul_one]
    show ∑ i, s p y' i * g i p y' = wchar ea u * ∑ i, s p y i * g i p y
    rw [← indep p y' _ e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hg _).2 p u y y' hyy, hadd, hw eb, ← hv]
    calc s p y i * ((v⁻¹ : (p.R)ˣ) : p.R) * (wchar ea u * (v : p.R) * g i p y)
        = wchar ea u * (s p y i * g i p y) * (((v⁻¹ : (p.R)ˣ) : p.R) * v) := by ring
      _ = wchar ea u * (s p y i * g i p y) := by rw [Units.inv_mul, mul_one]
  · intro i
    funext p y
    show (∑ i', s p y i' * g i' p y) * t i p y = g i p y
    calc (∑ i', s p y i' * g i' p y) * t i p y = ∑ i', s p y i' * (g i' p y * t i p y) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i', s p y i' * (g i p y * t i' p y) := by simp_rw [hc']
      _ = g i p y * ∑ i', s p y i' * t i' p y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i' _ => by ring
      _ = g i p y := by rw [hs, mul_one]

theorem glue_frPt : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ)
    (t g : Fin N → Rul (T.Q.Xo j) T.Q.c), (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) →
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    (∀ i, g i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) → (∀ i i', g i * t i' = g i' * t i) →
    ∃ h ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ i, h * t i = g i := by
  intro D T j a b n m N t g ht hunit hg hc
  have hg' : ∀ i, g i ∈ secW (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
      (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n + ex (T.Q.Dw j) b m) := by
    intro i; have := hg i; unfold sec at this; rwa [ex_add] at this
  exact glue_rules (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (ex (T.Q.Dw j) a n) (ex (T.Q.Dw j) b m) t g ht hunit hg' hc

theorem exists_evalAt_ne_zero {K : Type} [Field K] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    {N : ℕ} (t : Fin N → Rules pts)
    (hunit : ∀ (p : TRing K) (y : pts p.R), Ideal.span (Set.range fun i => t i p y) = ⊤)
    {S : Type} [CommRing S] [Nontrivial S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    ∃ i, evalAt pts mapR (t i) y ≠ 0 := by
  unfold evalAt
  simp only [dif_pos h]
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    ((hunit h.choose h.choose_spec.choose_spec.choose).symm ▸ Submodule.mem_top (x := (1 : h.choose.R)))
  by_contra hall
  push Not at hall
  have h1 := congrArg (fun r => h.choose_spec.choose r) hs
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_one, smul_eq_mul, map_mul, hall, mul_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

theorem exists_rdU_t_ne_zero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c),
    (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) →
    ∀ k x, x ∈ ((T.U j σ).X k).dom → ∃ i, rdU (T.U j σ) (t i) k x ≠ 0 := by
  intro D T hT j hj σ hσ N t hunit k x hx
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨i, hi⟩ := exists_evalAt_ne_zero (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) t hunit _ (hT.unTest j hj σ hσ k ⟨x, hx⟩)
  refine ⟨i, ?_⟩
  have e : rdU (T.U j σ) (t i) k x = toC (evR (T.Q.Xo j) T.Q.c (t i) ((T.U j σ).un k ⟨x, hx⟩)) := by
    classical
    exact dif_pos hx
  rw [e]
  exact hi

theorem span_of_products : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a b : (D.host.E →+* ℂ) × ℕ → ℕ) (n m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom a n → Dom b m → (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) → (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) → ∀ P ∈ offZero (T.U j σ).X, (∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c)))) → P ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T hT j hj σ hσ a b n m N t ha hb ht hunit P hP hPt

  have hrep : ∀ i, ∃ (L : ℕ) (cf : Fin L → ℂ) (g : Fin L → Rul (T.Q.Xo j) T.Q.c),
      (∀ l, g l ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m)) ∧
      ∑ l, cf l • rdU (T.U j σ) (g l) = P * rdU (T.U j σ) (t i) := by
    intro i
    obtain ⟨L, cf, g, hg⟩ := Submodule.mem_span_set'.1 (hPt i)
    choose g' hg' hg'e using fun l => (g l).2
    exact ⟨L, cf, g', hg', by rw [← hg]; simp [hg'e]⟩
  choose L cf g hg hsum using hrep

  let κ := Σ i : Fin N, Fin (L i)
  let A : κ → Fin N × Fin N → Rul (T.Q.Xo j) T.Q.c := fun q e =>
    (if q.1 = e.1 then g q.1 q.2 * t e.2 else 0) - (if q.1 = e.2 then g q.1 q.2 * t e.1 else 0)
  have hA : ∀ q e, A q e ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) := by
    intro q e
    have hm : ∀ i', g q.1 q.2 * t i' ∈ sec (T.Q.Xo j) T.Q.c (a + b + b) (n + m + m) :=
      fun i' => sec_mul _ _ _ _ _ _ (hg q.1 q.2) (ht i')
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;> first | exact hm _ | exact Submodule.zero_mem _
  have hdom : Dom (a + b + b) (n + m + m) :=
    ⟨fun τ => ((ha.1 τ).add (hb.1 τ)).add (hb.1 τ), (ha.2.add hb.2).add hb.2⟩

  have hrow : ∀ (z : κ → ℂ) (e : Fin N × Fin N), ∑ q, z q • rdU (T.U j σ) (A q e) =
      (∑ l, z ⟨e.1, l⟩ • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, z ⟨e.2, l⟩ • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) := by
    intro z e
    have h1 : ∀ q : κ, z q • rdU (T.U j σ) (A q e) =
        (if q.1 = e.1 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.2)) else 0) -
        (if q.1 = e.2 then z q • (rdU (T.U j σ) (g q.1 q.2) * rdU (T.U j σ) (t e.1)) else 0) := by
      intro q
      simp only [A]
      split_ifs <;> simp [map_sub, rdU_mul, smul_sub]
    simp only [h1, Finset.sum_sub_distrib]
    congr 1
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.1 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
    · rw [Fintype.sum_sigma, Finset.sum_eq_single e.2 (fun i' _ hi' => by simp [hi']) (by simp)]
      simp [Finset.sum_mul, smul_mul_assoc]
  let z : κ → ℂ := fun q => cf q.1 q.2
  have hz : ∀ e, ∑ q, z q • rdU (T.U j σ) (A q e) = 0 := by
    intro e
    rw [hrow]
    show (∑ l, cf e.1 l • rdU (T.U j σ) (g e.1 l)) * rdU (T.U j σ) (t e.2) -
      (∑ l, cf e.2 l • rdU (T.U j σ) (g e.2 l)) * rdU (T.U j σ) (t e.1) = 0
    rw [hsum, hsum]; ring
  have hzspan := _root_.GlobalTheory.kerC_span_rat D T j σ (GlobalTheory.rdIndep_of_lawsM D T.toCore hT.toLawsM j hj σ hσ) _ _ hdom κ (Fin N × Fin N) A hA z hz

  let S := Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c a n : Set (Rul (T.Q.Xo j) T.Q.c)))
  let Z : Submodule ℂ (κ → ℂ) :=
    { carrier := {z | ∃ Q ∈ S, ∀ i, Q * rdU (T.U j σ) (t i) = ∑ l, z ⟨i, l⟩ • rdU (T.U j σ) (g i l)}
      zero_mem' := ⟨0, S.zero_mem, fun i => by simp⟩
      add_mem' := by
        rintro z1 z2 ⟨Q1, hQ1, e1⟩ ⟨Q2, hQ2, e2⟩
        exact ⟨Q1 + Q2, S.add_mem hQ1 hQ2, fun i => by
          simp only [add_mul, e1, e2, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      smul_mem' := by
        rintro c z1 ⟨Q1, hQ1, e1⟩
        exact ⟨c • Q1, S.smul_mem c hQ1, fun i => by
          simp only [smul_mul_assoc, e1, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]⟩ }
  have hle : Submodule.span ℂ ((fun c : κ → T.Q.c.F => fun k => σ (c k)) ''
      {c | ∀ e, ∑ k, c k • A k e = 0}) ≤ Z := by
    rw [Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    let g' : Fin N → Rul (T.Q.Xo j) T.Q.c := fun i => ∑ l, c ⟨i, l⟩ • g i l
    have hg' : ∀ i, g' i ∈ sec (T.Q.Xo j) T.Q.c (a + b) (n + m) :=
      fun i => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hg i l)
    have hcomp : ∀ i i', g' i * t i' = g' i' * t i := by
      intro i i'
      have hrowR : ∑ q, c q • A q (i, i') = g' i * t i' - g' i' * t i := by
        have h1 : ∀ q : κ, c q • A q (i, i') =
            (if q.1 = i then c q • (g q.1 q.2 * t i') else 0) -
            (if q.1 = i' then c q • (g q.1 q.2 * t i) else 0) := by
          intro q
          simp only [A]
          split_ifs <;> simp [smul_sub]
        simp only [h1, Finset.sum_sub_distrib]
        congr 1
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
        · rw [Fintype.sum_sigma, Finset.sum_eq_single i' (fun i'' _ hi'' => by simp [hi'']) (by simp)]
          simp [g', Finset.sum_mul, smul_mul_assoc]
      have := hc (i, i')
      rw [hrowR] at this
      exact sub_eq_zero.1 this
    obtain ⟨h, hh, hht⟩ := glue_frPt D T j a b n m N t g' ht hunit hg' hcomp
    refine ⟨rdU (T.U j σ) h, Submodule.subset_span ⟨h, hh, rfl⟩, fun i => ?_⟩
    rw [← rdU_mul, hht]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [g', map_sum, map_smulₛₗ]
  obtain ⟨Q, hQ, hQe⟩ := hle hzspan

  have hQoff : Q ∈ offZero (T.U j σ).X := by
    refine (Submodule.span_le.2 ?_) hQ
    rintro _ ⟨f, _, rfl⟩
    exact rdU_mem_offZero _ f
  have hPQ : P = Q := by
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · obtain ⟨i, hi⟩ := exists_rdU_t_ne_zero D T hT j hj σ hσ N t hunit k x hx
      have e1 := congrFun (congrFun (hQe i) k) x
      have e2 := congrFun (congrFun (hsum i) k) x
      have : Q k x * rdU (T.U j σ) (t i) k x = P k x * rdU (T.U j σ) (t i) k x := by
        rw [show Q k x * rdU (T.U j σ) (t i) k x = (Q * rdU (T.U j σ) (t i)) k x from rfl, e1,
          show P k x * rdU (T.U j σ) (t i) k x = (P * rdU (T.U j σ) (t i)) k x from rfl, ← e2]
      exact (mul_right_cancel₀ hi this).symm
    · rw [hP k x hx, hQoff k x hx]
  rw [hPQ]; exact hQ

end GlobalTheory.GlueSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhere
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertLevel

section MixMat
variable {R : Type*} [CommRing R] {n : ℕ}

theorem mix_mul (p : R) (hp : p * p = p) (A B C D : Matrix (Fin n) (Fin n) R) :
    (p • A + (1 - p) • B) * (p • C + (1 - p) • D) = p • (A * C) + (1 - p) • (B * D) := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [mul_comm, h1]
  have h3 : (1 - p) * (1 - p) = 1 - p := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hp, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_one (p : R) : p • (1 : Matrix (Fin n) (Fin n) R) + (1 - p) • 1 = 1 := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem conjT_mix (σ : R →+* R) (p : R) (hp : σ p = p) (A B : Matrix (Fin n) (Fin n) R) :
    conjT σ (p • A + (1 - p) • B) = p • conjT σ A + (1 - p) • conjT σ B := by
  ext i j
  simp [conjT, map_sub, hp]

end MixMat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_GA_iff (x : GL (Fin n) (AL L)) :
    x ∈ ReciprocityTheory.Aut.GA L n ↔ (x : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x = 1 := Iff.rfl

def mixG (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) : GAf L n :=
  ⟨⟨p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)),
    p • ((g.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) +
      (1 - p) • ((h.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)),
    by rw [mix_mul p hp, Units.mul_inv, Units.mul_inv, mix_one],
    by rw [mix_mul p hp, Units.inv_mul, Units.inv_mul, mix_one]⟩, by
    rw [mem_GA_iff]
    show (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) *
      conjT (conjAL L) (p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L))) = 1
    rw [conjT_mix _ p hc, mix_mul p hp, (mem_GA_iff _).1 g.2, (mem_GA_iff _).1 h.2, mix_one]⟩

theorem mixG_val (p : AL L) (hp : p * p = p) (hc : conjAL L p = p) (g h : GAf L n) :
    ((mixG p hp hc g h).1 : Matrix (Fin n) (Fin n) (AL L)) =
      p • (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - p) • (h.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}


open GlobalTheory.InertUmax in
def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

section Idem
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))

theorem compAt_idemAt_self : compAt L v (idemAt v) = 1 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same, ← Algebra.TensorProduct.one_def]

theorem compAt_idemAt_ne {w} (hw : w ≠ v) : compAt L w (idemAt v) = 0 := by
  rw [idemAt, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self : idemAt (L := L) v * idemAt v = idemAt v := by
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · rw [compAt_idemAt_ne v hw]; simp

theorem conjAL_idemAt : conjAL L (idemAt v) = idemAt v := by
  simp [idemAt, conjAL, Algebra.TensorProduct.map_tmul]

theorem idemAt_mem : idemAt (L := L) v ∈ ALint L :=
  GlobalTheory.InertUmax.one_tmul_sgl_mem L v 1 (one_mem _)

theorem one_sub_idemAt_mem : 1 - idemAt (L := L) v ∈ ALint L :=
  Subring.sub_mem _ (one_mem _) (idemAt_mem v)

theorem one_entry_mem (S : Subring (AL L)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ S := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_entry (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem away_eq_zero {x : GAf L n} (hx : TrivOutside {v} x) (i j : Fin n) :
    (1 - idemAt v) * ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
  apply GlobalTheory.InertUmax.eq_zero_of_compAt
  intro w
  rw [map_mul, map_sub, map_sub, map_one, compAt_one_entry]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self]; simp
  · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
    rw [Matrix.map_apply] at h
    rw [h, sub_self, mul_zero]

end Idem

def DivBy (N : ℕ) (M : Matrix (Fin n) (Fin n) (AL L)) : Prop :=
  ∀ i j, ∃ y ∈ ALint L, M i j = (N : AL L) * y

theorem DivBy.add {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) (hB : DivBy N B) :
    DivBy N (A + B) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  obtain ⟨z, hz, f⟩ := hB i j
  exact ⟨y + z, Subring.add_mem _ hy hz, by rw [Matrix.add_apply, e, f, mul_add]⟩

theorem DivBy.neg {N : ℕ} {A : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A) : DivBy N (-A) := fun i j => by
  obtain ⟨y, hy, e⟩ := hA i j
  exact ⟨-y, Subring.neg_mem _ hy, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem DivBy.mul_int {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (A * B) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, y i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hB k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum, mul_assoc]⟩

theorem DivBy.int_mul {N : ℕ} {A B : Matrix (Fin n) (Fin n) (AL L)} (hA : DivBy N A)
    (hB : ∀ i j, B i j ∈ ALint L) : DivBy N (B * A) := fun i j => by
  choose y hy e using hA
  exact ⟨∑ k, B i k * y k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hB i k) (hy k j), by
    simp only [Matrix.mul_apply, e, Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring⟩

def levelAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧
    DivBy N ((1 - idemAt v) • ((κ.1 : Matrix (Fin n) (Fin n) (AL L)) - 1))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Umax L n).mul_mem ha hb, ?_⟩
    have e : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) * (b.1 : Matrix (Fin n) (Fin n) (AL L)) +
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul]
    exact (ha'.mul_int hb).add hb'
  one_mem' := ⟨(Umax L n).one_mem, fun i j => ⟨0, zero_mem _, by simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Umax L n).inv_mem ha, ?_⟩
    have e : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
        -(((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * ((a.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
      rw [mul_sub, mul_one]
      have : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
      rw [this]; abel
    rw [e, smul_neg, ← Matrix.mul_smul]
    exact (ha'.int_mul ((Umax L n).inv_mem ha)).neg

end GlobalTheory.InertLevel

namespace GlobalTheory.InertLevel

theorem exists_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  intro L _ _ _ n v N _
  have hp := idemAt_mul_self (L := L) v
  have hc := conjAL_idemAt (L := L) v
  refine ⟨levelAt (n := n) v N, ?_, ?_, ?_⟩
  · rintro κ ⟨hU, hκ⟩
    refine ⟨hU, fun i j => ?_⟩
    obtain ⟨y, hy, e⟩ := hκ i j
    refine ⟨(1 - idemAt v) * y, Subring.mul_mem _ (one_sub_idemAt_mem v) hy, ?_⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, e]; ring
  · intro κ hκ
    refine ⟨fun h => h.1, fun h => ⟨h, fun i j => ⟨0, zero_mem _, ?_⟩⟩⟩
    rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, away_eq_zero v hκ, mul_zero]
  · rintro κ ⟨hU, hκ⟩
    refine ⟨mixG (idemAt v) hp hc κ 1, mixG (idemAt v) hp hc 1 κ, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, mix_mul _ hp, OneMemClass.coe_one, Units.val_one,
        mul_one, one_mul]
      rw [← add_smul, add_sub_cancel, one_smul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (hU i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
    · intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
        smul_eq_mul, map_add, map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne v hw']
      simp only [OneMemClass.coe_one, Units.val_one, compAt_one_entry, zero_mul, zero_add, sub_zero, one_mul]
    · intro i j
      rw [mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact Subring.add_mem _ (Subring.mul_mem _ (idemAt_mem v) (by simpa using one_entry_mem (ALint L) i j))
        (Subring.mul_mem _ (one_sub_idemAt_mem v) (hU i j))
    · intro i j
      obtain ⟨y, hy, e⟩ := hκ i j
      refine ⟨y, hy, ?_⟩
      rw [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e
      rw [← e, mixG_val, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      simp only [OneMemClass.coe_one, Units.val_one]
      ring
    · intro x hx
      have hX : (x.1 : Matrix (Fin n) (Fin n) (AL L)) =
          idemAt v • (x.1 : Matrix (Fin n) (Fin n) (AL L)) + (1 - idemAt v) • 1 := by
        ext i j
        have h := away_eq_zero v hx i j
        rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
        linear_combination h
      apply Subtype.ext; apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, mixG_val, OneMemClass.coe_one, Units.val_one]
      rw [hX, mix_mul _ hp, mix_mul _ hp]
      simp only [mul_one, one_mul]

end GlobalTheory.InertLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBlockDetOfConjLower
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_block_det_of_conj_lower : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  first | (exact @GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (exact GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL) | (intros; apply GlobalTheory.SchurExt.AdBridge.schur_data_mul_finGL <;> assumption)
end

