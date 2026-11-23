module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixDegreeLeTwoMulOfUpperTriangular
section
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem GlobalTheory.Nef.deg_le_two_mul_of_triangular : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (g : Place k F → Matrix (Fin 2) (Fin 2) F), admitted g → (∀ v, g v 1 0 = 0) → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ 2 * b := by
  intro k F _ _ _ _ _ hFF g hg htri b hb
  by_cases hne : IsEmpty (Place k F)
  · have h0 : deg g = 0 := by simp [deg, finsum_of_isEmpty]
    have hres : IsRes (k := k) (F := F) (E := F) id := fun p x => by simp
    have hw : (![1, 0] : Fin 2 → F) ≠ 0 := by intro h; simpa using congrFun h 0
    have h1 := hb F id hres ![1, 0] hw
    have hl : degLine (pullAd id g) (![1, 0] : Fin 2 → F) = 0 := by simp [degLine, finsum_of_isEmpty]
    rw [hl] at h1
    simp at h1
    rw [h0]; push_cast; linarith
  rw [not_isEmpty_iff] at hne
  obtain ⟨v₀⟩ := hne
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.Nef.exists_section_of_large_deg k F hFF
  obtain ⟨π, hπ0, hπ⟩ := (_root_.GlobalTheory.Nef.ord_calculus k F v₀).2.2.2.2.2.1
  have key : ∀ m : ℕ, ((m * (m + 1) / 2 : ℕ) : ℝ) * (deg g : ℝ) ≤ (m + 1) * (m * b + 1 + γ) := by
    intro m
    set N : ℕ := m * (m + 1) / 2 with hN
    set S : Place k F → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun v => symMat m (g v) with hS
    obtain ⟨hSadm, hSdeg⟩ := GlobalTheory.Nef.admissible_degree_symmetricPowerFamily k F m g hg htri
    rw [← hN] at hSdeg
    set D : ℤ := (N : ℤ) * deg g - (m + 1) * γ - 1 with hD
    set e : ℤ := D / (m + 1) with he
    have hm0 : (0 : ℤ) < m + 1 := by positivity
    have hdiv := Int.mul_ediv_add_emod D (m + 1)
    have hmod0 := Int.emod_nonneg D hm0.ne'
    have hmod1 := Int.emod_lt_of_pos D hm0
    rw [← he] at hdiv
    obtain ⟨hTadm, hTdeg⟩ := GlobalTheory.Nef.admissible_degree_twistFamilyAtPlaceByScalar k F (m + 1) S hSadm v₀ π hπ0 hπ e
    have hdegT : ((m + 1 : ℕ) : ℤ) * γ < deg (twistAt v₀ (π ^ (-e)) S) := by
      have hc1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hTdeg, hSdeg, hc1]; linarith
    obtain ⟨p, hp0, hpint⟩ := hγ (m + 1) _ hTadm hdegT
    have hep : e ≤ degLine S p := _root_.GlobalTheory.Nef.degLine_ge_of_twist k F hFF (m + 1) S hSadm v₀ π hπ0 hπ e p hp0 hpint
    obtain ⟨E, _, _, _, c, s, t, hc, hst, hid⟩ := _root_.GlobalTheory.Nef.binary_form_splits F m p hp0
    letI : Algebra k E := ((algebraMap F E).comp (algebraMap k F)).toAlgebra
    haveI : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨ρ, hρ⟩ := (_root_.GlobalTheory.Nef.place_res_exists_pow k F E).1
    have hEFF : IsFF k E := (_root_.GlobalTheory.Nef.isFF_main k F hFF).2 E
    have pS := _root_.GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank k F E hFF ρ hρ (m + 1) S hSadm
    have pg := _root_.GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank k F E hFF ρ hρ 2 g hg
    have hpull : pullAd ρ S = fun P => symMat m (pullAd ρ g P) := by
      funext P; simp only [pullAd, hS, symMat_map]
    have htriE : ∀ P, pullAd ρ g P 1 0 = 0 := by intro P; simp [pullAd, htri]
    set q : Fin (m + 1) → E := fun i => algebraMap F E (p i) with hq
    have hpt : ∀ P, ordVec P ((symMat m (pullAd ρ g P)).mulVec q) =
        ord P c + ∑ j, ordVec P ((pullAd ρ g P).mulVec ![s j, t j]) := fun P =>
      _root_.GlobalTheory.Nef.ordVec_symMat_mulVec_triangular k E P m _ (htriE P) (pg.1.1 P) q c s t hc hst (by
        have h3 := hid E[X] (C ((pullAd ρ g P) 0 0)) (C ((pullAd ρ g P) 0 1) + C ((pullAd ρ g P) 1 1) * X)
        rw [Polynomial.algebraMap_eq] at h3
        exact h3)
    have h6 := _root_.GlobalTheory.Nef.degLine_eq_sum_of_split k E hEFF m (m + 1) (pullAd ρ g) pg.1 (fun P => symMat m (pullAd ρ g P)) q c
      (fun j => ![s j, t j]) hc hst hpt
    have h2 := pS.2.2.1 p hp0
    rw [hpull] at h2
    have hbound : ∀ j, (degLine (pullAd ρ g) ![s j, t j] : ℝ) ≤ b * Module.finrank F E :=
      fun j => hb E ρ hρ _ (hst j)
    have hsum : ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) ≤ m * (b * Module.finrank F E) := by
      push_cast
      calc (∑ j : Fin m, (degLine (pullAd ρ g) ![s j, t j] : ℝ)) ≤ ∑ _j : Fin m, b * Module.finrank F E :=
            Finset.sum_le_sum fun j _ => hbound j
        _ = m * (b * Module.finrank F E) := by simp
    have hfr : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
    have h7 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ m * (b * Module.finrank F E) := by
      have h8 : (Module.finrank F E : ℤ) * degLine S p = ∑ j, degLine (pullAd ρ g) ![s j, t j] := by
        rw [← h6, ← h2]
      have h8' : (Module.finrank F E : ℝ) * (degLine S p : ℝ) = ((∑ j, degLine (pullAd ρ g) ![s j, t j] : ℤ) : ℝ) := by
        exact_mod_cast h8
      have h9 : (e : ℝ) ≤ (degLine S p : ℝ) := by exact_mod_cast hep
      have h10 : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (degLine S p : ℝ) :=
        mul_le_mul_of_nonneg_left h9 hfr.le
      linarith
    have hemb : (e : ℝ) ≤ m * b := by
      have : (Module.finrank F E : ℝ) * (e : ℝ) ≤ (Module.finrank F E : ℝ) * (m * b) := by linarith
      exact le_of_mul_le_mul_left this hfr
    have hint : (N : ℤ) * deg g ≤ (m + 1) * (e + 1 + γ) := by linarith
    have hreal : ((N : ℤ) : ℝ) * (deg g : ℝ) ≤ ((m : ℝ) + 1) * ((e : ℝ) + 1 + γ) := by exact_mod_cast hint
    push_cast at hreal
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hpos : (0 : ℝ) < (deg g : ℝ) - 2 * b := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (1 + γ) / ((deg g : ℝ) - 2 * b))
  have hk := key m
  have hN : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * (m + 1) / 2 := by
    have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  rw [hN] at hk
  rw [div_lt_iff₀ hpos] at hm
  have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : (m : ℝ) * (deg g : ℝ) ≤ 2 * (m * b + 1 + γ) := by
    have h3 : ((m : ℝ) + 1) * ((m : ℝ) * (deg g : ℝ)) ≤ ((m : ℝ) + 1) * (2 * (m * b + 1 + γ)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hm'
  nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairRestrictionInjectiveFirstCohomology
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem exists_cob_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (f : Z1 (OAff s'))
    (g : ∀ p : Pair φ, (OAff s').obj (op p.1.1))
    (hg : ∀ (p q : Pair φ) (hqp : q ≤ p), f.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
      g q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g p)) :
    ∃ G : C0 (OAff s'), d0 (OAff s') G = f.1 ∧ ∀ (W : X'.affineOpens) (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op (G (op W)) = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
  have ex : ∀ W : X'.affineOpens, ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W),
      mp (OAff s') (homOfLE hp).op G = g p - f.1 (op W) (op p.1.1) (homOfLE hp).op := by
    intro W
    refine _root_.GlobalTheory.CechDR.pair_glue φ s' W _ fun p q hp hq hqp ↦ ?_
    have e := Z1.comp f (homOfLE hp).op (homOfLE (Pair.le_fst hqp)).op
    rw [show (homOfLE hp).op ≫ (homOfLE (Pair.le_fst hqp)).op = (homOfLE hq).op from rfl, hg p q hqp] at e
    rw [map_sub, e]
    ring
  choose G hG using ex
  refine ⟨fun T ↦ G T.unop, ?_, hG⟩
  funext T T' a
  refine sec_eq_of_pair φ s' T'.unop _ _ fun p hp ↦ ?_
  have e1 := Z1.comp f a (homOfLE hp).op
  have e2 : a ≫ (homOfLE hp).op = (homOfLE (hp.trans (leOfHom a.unop))).op := rfl
  rw [e2] at e1
  rw [amitsur_d0_apply, map_sub, ← mp_comp, e2, hG, hG]
  linear_combination e1

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential

theorem pairRes_injective : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R'), Function.Injective (pairRes φ s').pull1 ∧
      Function.Injective (pullGlob1 (pairRes φ s')) ∧ Function.Injective (pullHyp1 (pairRes φ s')) := by
  intro R' _ X X' φ s'
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    obtain ⟨G, hG, -⟩ := exists_cob_of_pair φ s' f (fun p ↦ g (op p)) fun p q hqp ↦
      (congrFun (congrFun (congrFun hg (op p)) (op q)) (homOfLE hqp).op).symm
    exact H1.mk_eq_zero.2 ⟨G, hG⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    have h0 : ∀ p : Pair φ, ω.1 (op p.1.1) = 0 := fun p ↦
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) (op p) _).symm.trans
        (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 (op p)) hω)
    refine Subtype.ext (funext fun W ↦ GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop _ fun p hp ↦ ?_)
    rw [← ω.2 (homOfLE hp).op]
    exact h0 p
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Hyp1.mk_surjective _ c
    rw [pullHyp1_mk, Hyp1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ p : Pair φ, (OAff s').obj (op p.1.1) := fun p ↦ g (op p)
    have hf : ∀ (p q : Pair φ) (hqp : q ≤ p), z.1.1 (op p.1.1) (op q.1.1) (homOfLE (Pair.le_fst hqp)).op =
        g' q - mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (g' p) := fun p q hqp ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.1 (op p) (op q) (homOfLE hqp).op) hg).symm
    have hω : ∀ p : Pair φ, D R' _ (g' p) = z.1.2 (op p.1.1) := fun p ↦
      (congrArg (fun c : Tot1 (OPair φ s') ↦ c.2 (op p)) hg).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor _ _ _ _)
    obtain ⟨G, hG, hGp⟩ := exists_cob_of_pair φ s' (cechDeRhamTotalCocyclesOne.fn _ z) g' hf
    refine Hyp1.mk_eq_zero.2 ⟨G, Tot1.ext (fun T T' a ↦ congrFun (congrFun (congrFun hG T) T') a)
      fun W ↦ ?_⟩
    refine (sub_eq_zero.1 (GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs φ s' W.unop (D R' _ (G W) - z.1.2 W) fun p hp ↦ ?_))
    have e := cechDeRhamTotalCocyclesOne.conn z (homOfLE hp).op
    rw [map_sub, p1_D, hGp, map_sub, hω]
    change _ - (p1 _ _ _) = _
    rw [e, show ((cechDeRhamTotalCocyclesOne.fn (OAff s') z : Z1 (OAff s')) : C1 (OAff s')) = z.1.1 from rfl]
    abel

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisObjectsUnitLociCoverAbove
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
private lemma covBy_of_covBy_localizations {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : C → Prop) (hLoc : _root_.GlobalTheory.CatCoh.Desc.HasLoc F) (T : C)
    {n : ℕ} (c : Fin n → F.obj T) (hc : Ideal.span (Set.range c) = ⊤)
    (h : ∀ (j : Fin n) (L : C) (l : T ⟶ L), IsUnit (_root_.GlobalTheory.CatCoh.mp F l (c j)) →
      (∀ (S : C) (w : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F w (c j)) → ∃! v, l ≫ v = w) →
      _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P L) :
    _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P T := by
  have hL := fun j => hLoc T (c j)
  choose L l hlu hsurj hker huniv using hL
  have hcov := fun j => h j (L j) (l j) (hlu j) (huniv j)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy at hcov
  choose m e he hP using hcov
  choose N x hx using fun j k => hsurj j (e j k)
  let b' : (Σ j : Fin n, Fin (m j)) → F.obj T := fun p => x p.1 p.2 * c p.1
  have hspan' : Ideal.span (Set.range b') = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hc, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (1 : F.obj (L j)) ∈ Ideal.span (Set.range (e j)) := by
      rw [he j]; exact Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose N' s hs using fun k => hsurj j (r k)
    have hq : ∀ k, ∃ q, (∑ k', (N' k' + N j k')) = N' k + N j k + q := fun k =>
      Nat.exists_eq_add_of_le (Finset.single_le_sum (f := fun k' => N' k' + N j k')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    choose q hq using hq
    have hterm : ∀ k, _root_.GlobalTheory.CatCoh.mp F (l j) (s k * x j k * c j ^ q k) =
        (r k • e j k) * _root_.GlobalTheory.CatCoh.mp F (l j) (c j) ^ (∑ k', (N' k' + N j k')) := by
      intro k
      rw [map_mul, map_mul, map_pow, ← hs k, ← hx j k, hq k, pow_add, pow_add, smul_eq_mul]
      ring
    have hz : _root_.GlobalTheory.CatCoh.mp F (l j)
        (c j ^ (∑ k', (N' k' + N j k')) - ∑ k, s k * x j k * c j ^ q k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, hr,
        one_mul, map_pow, sub_self]
    obtain ⟨M, hM⟩ := hker j _ hz
    refine ⟨M + (∑ k', (N' k' + N j k')) + 1, ?_⟩
    have h2 : c j ^ M * c j ^ (∑ k', (N' k' + N j k')) =
        c j ^ M * ∑ k, s k * x j k * c j ^ q k := by
      rw [← sub_eq_zero, ← mul_sub]; exact hM
    have h3 : c j ^ (M + (∑ k', (N' k' + N j k')) + 1) =
        ∑ k, (c j ^ M * s k * c j ^ q k) * b' ⟨j, k⟩ := by
      rw [pow_succ, pow_add, h2, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [b']
      ring
    rw [h3]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, k⟩, rfl⟩)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  let eqv := Fintype.equivFin (Σ j : Fin n, Fin (m j))
  refine ⟨Fintype.card (Σ j : Fin n, Fin (m j)), b' ∘ eqv.symm, ?_, ?_⟩
  · rw [Set.range_comp, eqv.symm.range_eq_univ, Set.image_univ]
    exact hspan'
  · intro i S w hw
    change IsUnit (_root_.GlobalTheory.CatCoh.mp F w
      (x (eqv.symm i).1 (eqv.symm i).2 * c (eqv.symm i).1)) at hw
    generalize eqv.symm i = p at hw
    obtain ⟨j, k⟩ := p
    rw [map_mul, IsUnit.mul_iff] at hw
    obtain ⟨hxw, hcw⟩ := hw
    obtain ⟨v, hv, -⟩ := huniv j S w hcw
    apply hP j k S v
    have hfac : _root_.GlobalTheory.CatCoh.mp F w (x j k) = _root_.GlobalTheory.CatCoh.mp F v (e j k) *
        (_root_.GlobalTheory.CatCoh.mp F v (_root_.GlobalTheory.CatCoh.mp F (l j) (c j))) ^ (N j k) := by
      rw [← hv, _root_.GlobalTheory.CatCoh.mp_comp, ← hx j k, map_mul, map_pow]
    rw [hfac, IsUnit.mul_iff] at hxw
    exact hxw.1


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
theorem _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → _root_.GlobalTheory.CatCoh.Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  intro R _ C _ C' _ F G _ _ hLoc hbasis hB T n d hd t u
  apply covBy_of_covBy_localizations F _ hLoc (G.obj t)
    (fun j => _root_.GlobalTheory.CatCoh.mp F u (d j)) (_root_.GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top F u hd)
  intro j L l hl _
  obtain ⟨m, e, he, hfac⟩ := hbasis L
  apply covBy_of_covBy_localizations F _ hLoc L e he
  intro k L' l' hl' _
  obtain ⟨t'', v₁, v₂, -⟩ := hfac k L' l' hl'
  obtain ⟨p, f, hf, hP⟩ := hB t t'' L' (l ≫ l') v₂
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  refine ⟨p, f, hf, ?_⟩
  intro i S'' z hz
  obtain ⟨t₃, ⟨c₁⟩, ⟨c₂⟩, ⟨w⟩⟩ := hP i S'' z hz
  refine ⟨t₃, c₁, ⟨j, ?_⟩, ⟨w⟩⟩
  have hunit : IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ l ≫ v₁ ≫ G.map c₂) (d j)) := by
    rw [_root_.GlobalTheory.CatCoh.mp_comp]
    exact _root_.GlobalTheory.CatCoh.Desc.isUnit_comp (v₁ ≫ G.map c₂) hl
  rwa [show u ≫ G.map c₁ = u ≫ l ≫ v₁ ≫ G.map c₂ from Subsingleton.elim _ _]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingLocalizationMembership
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem stdForm_incl_map_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  show t (algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)) = algebraMap F F' ((γ : Matrix (Fin n) (Fin n) F) i j)
  exact t.commutes _

theorem stdForm_adjoin_map_mem {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (γ : GL (Fin n) F) {M : Matrix (Fin n) (Fin n) F'}
    (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}) :
    M.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  let T : Matrix (Fin n) (Fin n) F' →+* Matrix (Fin n) (Fin n) F' := ((t : F' ≃+* F') : F' →+* F').mapMatrix
  have hT : ∀ N, T N = N.map t := fun N => rfl
  rw [← hT]
  induction hM using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [hT, stdForm_incl_map_eq]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : T (algebraMap F' (Matrix (Fin n) (Fin n) F') r) = algebraMap F' (Matrix (Fin n) (Fin n) F') (t r) := by
      rw [hT]
      ext i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem stdForm_commute_iff {F' : Type} [Field F'] {n : ℕ} (x y : GL (Fin n) F') :
    Commute x y ↔ Commute (x : Matrix (Fin n) (Fin n) F') (y : Matrix (Fin n) (Fin n) F') := by
  simp only [Commute, SemiconjBy, Units.ext_iff, Units.val_mul]

theorem isNorm_exists_twistedConj_adjoin :
    ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
      (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F') (γ : GL (Fin n) F),
      IsNorm s δ γ → ∃ y : GL (Fin n) F', ((y⁻¹ * δ * galAct F F' n s y : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
        nrm s (y⁻¹ * δ * galAct F F' n s y) = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n δ γ hN
  obtain ⟨_, -, h3, h4, h5⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n

  have hgfix : ∀ t : F' ≃ₐ[F] F', galAct F F' n t (incl F F' n γ) = incl F F' n γ := fun t =>
    Units.ext (stdForm_incl_map_eq n t γ)

  have hC : ∀ z w : GL (Fin n) F',
      (z : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} →
      Commute w (incl F F' n γ) → Commute z w := by
    intro z w hz hw
    rw [stdForm_commute_iff] at hw ⊢
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hz hw).symm
  have hCt : ∀ (t : F' ≃ₐ[F] F') (w : GL (Fin n) F'), Commute w (incl F F' n γ) →
      Commute (galAct F F' n t w) (incl F F' n γ) := by
    intro t w hw
    have := hw.map (galAct F F' n t)
    rwa [hgfix t] at this

  obtain ⟨c, hc⟩ := isConj_iff.1 hN
  have hn1 : nrm s (c⁻¹ * δ * galAct F F' n s c) = incl F F' n γ := by
    rw [h3, ← hc]; group
  have hcomm1 : Commute (c⁻¹ * δ * galAct F F' n s c) (incl F F' n γ) := by
    have := h4 (c⁻¹ * δ * galAct F F' n s c)
    rw [hn1, hgfix s] at this
    exact this

  obtain ⟨δ₀, hδ₀A, hn0⟩ := GlobalTheory.T.norm_map_surjective_finite_field F F' s hs n γ
  have hδ₀g : Commute δ₀ (incl F F' n γ) := hC δ₀ _ hδ₀A (Commute.refl _)
  have hεg : Commute (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (incl F F' n γ) :=
    (hδ₀g.inv_left).mul_left hcomm1
  have hεn : nrm s (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) = 1 := by
    have hp := h5 δ₀ (δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c)) (fun t u =>
      hC _ _ (by rw [show ((galAct F F' n t δ₀ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
        (δ₀ : Matrix (Fin n) (Fin n) F').map t from rfl]; exact stdForm_adjoin_map_mem n t γ hδ₀A) (hCt u _ hεg))
    rw [mul_inv_cancel_left, hn1, hn0] at hp
    exact (mul_eq_left.1 hp.symm)

  have hBst : ∀ M ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      M.map s ∈ Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    intro M hM
    rw [Subalgebra.mem_centralizer_iff] at hM ⊢
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    have e := congrArg (fun N => ((s : F' ≃+* F') : F' →+* F').mapMatrix N) (hM _ rfl)
    simp only [map_mul] at e
    rw [← stdForm_incl_map_eq n s γ]
    exact e
  have hεB : ((δ₀⁻¹ * (c⁻¹ * δ * galAct F F' n s c) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈
      Subalgebra.centralizer F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g' hg'
    rw [Set.mem_singleton_iff] at hg'
    subst hg'
    exact ((stdForm_commute_iff _ _).1 hεg).eq.symm
  obtain ⟨x, hxB, hεx⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n _ hBst _ hεB hεn
  have hxg : Commute x (incl F F' n γ) := by
    rw [stdForm_commute_iff]
    exact ((Subalgebra.mem_centralizer_iff F').1 hxB _ rfl).symm
  have hxδ₀ : Commute δ₀ x := hC δ₀ x hδ₀A hxg
  have e1 : c⁻¹ * δ * galAct F F' n s c = δ₀ * (x⁻¹ * galAct F F' n s x) := by
    rw [← hεx, mul_inv_cancel_left]
  have key : (c * x⁻¹)⁻¹ * δ * galAct F F' n s (c * x⁻¹) = δ₀ := by
    rw [map_mul, map_inv]
    calc (c * x⁻¹)⁻¹ * δ * (galAct F F' n s c * (galAct F F' n s x)⁻¹)
        = x * (c⁻¹ * δ * galAct F F' n s c) * (galAct F F' n s x)⁻¹ := by group
      _ = x * δ₀ * x⁻¹ := by rw [e1]; group
      _ = δ₀ := by rw [← hxδ₀.eq]; group
  exact ⟨c * x⁻¹, by rw [key]; exact hδ₀A, by rw [key]; exact hn0⟩

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  first | exact @GlobalTheory.CMVal.OrderUnits.orderC_units | exact GlobalTheory.CMVal.OrderUnits.orderC_units | (intros; apply GlobalTheory.CMVal.OrderUnits.orderC_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits : ∀ (N M : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact M (coAug g)) → ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → WExact N (coAug g) := by
  first | (exact @GlobalTheory.EtC.wExact_of_finiteType_iso) | (exact GlobalTheory.EtC.wExact_of_finiteType_iso) | (intros; apply GlobalTheory.EtC.wExact_of_finiteType_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLiftStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_injective | exact GlobalTheory.CechDR.pullHyp2_restrict_injective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_injective <;> assumption)
end

