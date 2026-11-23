module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientsAcyclicOfTwoSectionsRetraction
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory

theorem coef_acyclic_of_two_sections (C : Type 1) [Category.{0} C] (M : Coef C) (S : C ⥤ C) (u v : 𝟭 C ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (hr : ∀ (T T' : C) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x))
    (hu : ∀ T x, r T (M.map (u.app T) x) = 0) (hv : ∀ T x, r T (M.map (v.app T) x) = x) :
    M.Ac0 ∧ M.Ac1 ∧ M.Ac2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    funext T
    have h1 : g (S.obj T) = M.map (u.app T) (g T) := hg T (S.obj T) (u.app T)
    have h2 : g (S.obj T) = M.map (v.app T) (g T) := hg T (S.obj T) (v.app T)
    have e := hv T (g T)
    rw [← h2, h1, hu] at e
    exact e.symm
  · intro f hf
    refine ⟨fun T ↦ r T (f T (S.obj T) (u.app T) - f T (S.obj T) (v.app T)), ?_⟩
    intro T T' φ
    have key : ∀ θ : 𝟭 C ⟶ S, r T' (M.map (θ.app T') (f T T' φ)) + r T' (f T' (S.obj T') (θ.app T')) =
        M.map φ (r T (f T (S.obj T) (θ.app T))) + r T' (f (S.obj T) (S.obj T') (S.map φ)) := by
      intro θ
      have nat : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have e1 := hf T T' (S.obj T') φ (θ.app T')
      have e2 := hf T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
      rw [nat, e2] at e1
      have e3 := congrArg (r T') e1
      simp only [map_add (f := _), hr] at e3
      exact e3.symm
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) kv - ku
  · intro z hz
    let A : (𝟭 C ⟶ S) → ∀ (T T' : C) (_ : T ⟶ T'), M.obj (S.obj T') := fun θ T T' φ ↦
      z T T' (S.obj T') φ (θ.app T') - z T (S.obj T) (S.obj T') (θ.app T) (S.map φ)
    refine ⟨fun T T' φ ↦ r T' (A v T T' φ - A u T T' φ), ?_⟩
    intro T T' T'' φ ψ
    have key : ∀ θ : 𝟭 C ⟶ S, M.map ψ (r T' (A θ T T' φ)) =
        r T'' (M.map (θ.app T'') (z T T' T'' φ ψ)) + r T'' (A θ T T'' (φ ≫ ψ)) - r T'' (A θ T' T'' ψ)
          - r T'' (z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ)) := by
      intro θ
      have nat1 : φ ≫ θ.app T' = θ.app T ≫ S.map φ := θ.naturality φ
      have nat2 : ψ ≫ θ.app T'' = θ.app T' ≫ S.map ψ := θ.naturality ψ
      have h1 := hz T T' T'' (S.obj T'') φ ψ (θ.app T'')
      have h2 := hz T T' (S.obj T') (S.obj T'') φ (θ.app T') (S.map ψ)
      have h3 := hz T (S.obj T) (S.obj T') (S.obj T'') (θ.app T) (S.map φ) (S.map ψ)
      rw [nat1, ← nat2] at h2
      rw [← S.map_comp] at h3
      have inner : M.map (S.map ψ) (A θ T T' φ) =
          M.map (θ.app T'') (z T T' T'' φ ψ) + A θ T T'' (φ ≫ ψ) - A θ T' T'' ψ
            - z (S.obj T) (S.obj T') (S.obj T'') (S.map φ) (S.map ψ) := by
        simp only [A, map_sub]
        first
          | linear_combination (norm := abel1) h2 - h3 - h1
          | linear_combination (norm := abel1) h2 - h3 + h1
          | linear_combination (norm := abel1) h1 + h2 - h3
          | linear_combination (norm := abel1) -h1 - h2 + h3
      rw [← hr, inner]
      simp only [map_sub, map_add (f := _)]
    have ku := key u
    have kv := key v
    rw [hu] at ku
    rw [hv] at kv
    simp only [map_sub]
    linear_combination (norm := abel1) ku - kv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyVanishesArtinian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  first | (exact @GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (exact GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (intros; apply GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolutionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X), Hyp R Φ a → ∀ n, WExact (term (Φ ⋙ HC R F) n) a := by
  first | exact @GlobalTheory.EtC.wExact_term_HC | exact GlobalTheory.EtC.wExact_term_HC | (intros; apply GlobalTheory.EtC.wExact_term_HC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductAssocOfPairingAssoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sum_range_triangle {A : Type*} [AddCommMonoid A] (G : ℕ → ℕ → A) (N : ℕ) :
    ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun y _ => ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    rfl

theorem Sx.sub_congr {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {j j' l : ℕ} (hj : j = j') (h : j + l ≤ N)
    (h' : j' + l ≤ N) : x.sub j l h = x.sub j' l h' := by
  subst hj
  rfl

theorem Pair.mul_ev_congr {R : Type} [CommRing R] {J K M : Cx R} (μ : Pair J K M) {E : Spc} {k : ℤ}
    (γ : Cochain ((chains R).obj E) K k) {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (t tu : ℤ) (b : Sec (J.X t) U)
    {a a' j j' : ℕ} (ha : a = a') (hj : j = j') (hx : j + a ≤ N) (hx' : j' + a' ≤ N)
    (h : t + (-(a : ℤ) + k) = tu) (h' : t + (-(a' : ℤ) + k) = tu) :
    μ.mul U t (-(a : ℤ) + k) tu h b (ev γ a _ rfl U (x.sub j a hx)) =
      μ.mul U t (-(a' : ℤ) + k) tu h' b (ev γ a' _ rfl U (x.sub j' a' hx')) := by
  subst ha hj
  rfl

end GlobalTheory.EtC

theorem GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  intro R _ I J K M M' L μ ν μ' ν' hA E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h1).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ h1).2 α β δ hδ]
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν h2).1 δ γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν h2).2 δ γ ε hε]
  obtain ⟨δ', hδ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).1 β γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).2 β γ δ' hδ']
  obtain ⟨ε', hε'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).1 α δ'
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).2 α δ' ε' hε']
  suffices hh : ε.1 = ε'.1 by rw [show ε = ε' from Subtype.ext hh]
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := w)).2.2.1
  intro N s hs U x
  rw [hε N s hs U x, hε' N s hs U x]
  have ss := fun {N' : ℕ} (y : Sx E N' U) => (GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite y).1
  let G : ℕ → ℕ → Sec (L.X s) U := fun p r => if hpr : p + r ≤ N then
    (((mk * (p : ℤ) + k * (r : ℤ)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α.1 p _ rfl U (x.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β.1 r _ rfl U (x.sub p r hpr)) (ev γ.1 (N - p - r) _ rfl U (x.sub (p + r) (N - p - r) (by omega))))
    else 0
  trans ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p)
  · rw [← Fin.sum_univ_eq_sum_range (fun P => ∑ p ∈ Finset.range (P + 1), G p (P - p)) (N + 1)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.isLt
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hδ (P : ℕ) _ _ U (x.sub 0 (P : ℕ) (by omega)), map_sum, LinearMap.sum_apply, Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun p => G p ((P : ℕ) - p)) ((P : ℕ) + 1)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp := p.isLt
    simp only [G]
    rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, LinearMap.smul_apply, smul_smul,
      ← Units.val_mul, ← Int.negOnePow_add]
    rw [hA (tu := -((N - (p : ℕ) : ℕ) : ℤ) + mk)]
    rotate_left
    · omega
    · omega
    rw [ss, ss, GlobalTheory.EtC.Sx.sub_congr x (show 0 + 0 = 0 from rfl) _ (by omega),
      GlobalTheory.EtC.Sx.sub_congr x (show 0 + (p : ℕ) = p by omega) _ (by omega)]
    rw [GlobalTheory.EtC.Pair.mul_ev_congr μ' γ.1 x _ _ _ (a' := N - (p : ℕ) - ((P : ℕ) - (p : ℕ)))
      (j' := (p : ℕ) + ((P : ℕ) - (p : ℕ))) (by omega) (by omega) _ (by omega) _ (by omega)]
    have hsg : (k * ((P : ℕ) : ℤ) + m * ((p : ℕ) : ℤ)).negOnePow =
        (mk * ((p : ℕ) : ℤ) + k * (((P : ℕ) - (p : ℕ) : ℕ) : ℤ)).negOnePow := by
      congr 1
      rw [Nat.cast_sub (by omega), ← h3]
      ring
    rw [hsg]
  trans ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r
  · exact GlobalTheory.EtC.sum_range_triangle G N
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), G p r) (N + 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.isLt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hδ' (N - (p : ℕ)) _ _ U (x.sub (p : ℕ) (N - (p : ℕ)) (by omega)), map_sum, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun r => G p r) (N - (p : ℕ) + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := r.isLt
  simp only [G]
  rw [dite_eq_left (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add, ss, ss]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitneyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (exact GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (intros; apply GlobalTheory.PBFc.cup_cast_mk_of_isAW  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductDiscreteSpaceFibreEqPairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing : ∀ (q N : ℕ) (F : PSh) {n m i₁ i₂ : ℤ} (α : Cocycle ((chains (ZMod q)).obj (disc.obj F)) (res (ZMod q) (tw q i₁)) n) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) m), (∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0) → ∃ γ : Cocycle ((chains (ZMod q)).obj (disc.obj F ⨯ fibQ q N)) (res (ZMod q) (tw q (i₁ + i₂))) (n + m), CohomologyClass.mk γ = cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk α)) (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (CohomologyClass.mk z)) ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + (n + m) = s) (V : Scheme.{0}) (w : Sx (disc.obj F ⨯ fibQ q N) k V), _root_.GlobalTheory.EtC.ev (R := ZMod q) γ.1 k s hs V w = (twPair q i₁ i₂).mul V n (-(k : ℤ) + m) s (by omega) (_root_.GlobalTheory.EtC.ev (R := ZMod q) α.1 0 n (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) w)) (_root_.GlobalTheory.EtC.ev (R := ZMod q) z.1 k (-(k : ℤ) + m) rfl V (Sx.map prod.snd w)) := by
  first | (exact @GlobalTheory.EtC.disc_cup_fibre) | (exact GlobalTheory.EtC.disc_cup_fibre) | (intros; apply GlobalTheory.EtC.disc_cup_fibre  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cup_natural_in_pairing : ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b) := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ]
  simp only [cpush, cpost_mk]
  refine ((GlobalTheory.T.cup_eq_class_of_isAW R ν hk).2 _ _ _ ?_).symm
  intro N w h U x
  have hm := fun {L L' : Cx R} (φ : L ⟶ L') {d : ℤ} (c : Cochain ((chains R).obj E) L d) p s hs U x =>
    (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := d)).2.2.2.2 φ c p s hs U x
  change ev (γ.1.comp (Cochain.ofHom u) (add_zero k)) N w h U x = _
  rw [hm, hγ N w h U x]
  refine (map_sum ((u.f w).hom.app (op U)).hom _ _).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  change Sec.map (u.f w) _ = _ • ν.mul U _ _ w _ (ev (α.1.comp (Cochain.ofHom f) (add_zero n)) _ _ _ U _) (ev (β.1.comp (Cochain.ofHom g) (add_zero m)) _ _ _ U _)
  rw [hm, hm, Units.smul_def, Units.smul_def, ← hc]
  exact map_zsmul ((u.f w).hom.app (op U)).hom _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLatticePrimeScaling
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.NormSurj

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem coe_galAct (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  rfl

theorem map_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  simp [incl, gal]

theorem adjoin_stable (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ∀ x ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      x.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx, map_incl]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : (algebraMap F' (Matrix (Fin n) (Fin n) F') r).map t = algebraMap F' _ (t r) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add t)]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have := Matrix.map_mul (L := x) (M := y) (f := (t : F' →+* F'))
    erw [this]; exact Subalgebra.mul_mem _ hx hy

theorem adjoin_comm {A : Type} [Ring A] [Algebra F' A] (M : A) :
    ∀ x ∈ Algebra.adjoin F' {M}, ∀ y ∈ Algebra.adjoin F' {M}, x * y = y * x := by
  intro x hx y hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hx
  obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).1 hy
  rw [← map_mul, mul_comm, map_mul]

theorem inv_mem_of_finite {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (δ : GL (Fin n) F') (h : (δ : Matrix (Fin n) (Fin n) F') ∈ B) :
    ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
  haveI : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))
  let f : B → B := fun b => ⟨δ, h⟩ * b
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (δ : Matrix (Fin n) (Fin n) F') * a = δ * b := congrArg Subtype.val hab
    apply Subtype.ext
    have h2 := congrArg (fun m => ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * m) h1
    simpa [← mul_assoc] using h2
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hf) 1
  have hb' : (δ : Matrix (Fin n) (Fin n) F') * b = 1 := congrArg Subtype.val hb
  have : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = b := by
    calc ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')
        = ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (δ * b) := by rw [hb', mul_one]
      _ = b := by rw [← mul_assoc]; simp
  rw [this]; exact b.2

def unitsIn {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) :
    Subgroup (GL (Fin n) F') where
  carrier := {δ | (δ : Matrix (Fin n) (Fin n) F') ∈ B}
  one_mem' := by simpa using B.one_mem
  mul_mem' := fun ha hb => by simpa using B.mul_mem ha hb
  inv_mem' := fun h => inv_mem_of_finite B _ h

theorem nrm_surj_adjoin : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F',
      (δ : Matrix (Fin n) (Fin n) F') ∈
        Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
      nrm s δ = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n γ
  set M : Matrix (Fin n) (Fin n) F' := ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') with hM
  set B := Algebra.adjoin F' {M} with hB
  obtain ⟨hfix, hinj, -, hcomm4, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hcard := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B (adjoin_stable n s γ)
  have hstab : ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), δ ∈ unitsIn B → galAct F F' n t δ ∈ unitsIn B :=
    fun t δ h => by
      show ((galAct F F' n t δ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B
      rw [coe_galAct]; exact adjoin_stable n t γ _ h
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := adjoin_comm M
  have hcommU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, δ * ε = ε * δ := fun δ hδ ε hε =>
    Units.ext (by simpa using hcommB _ hδ _ hε)
  have hnrm_mem : ∀ δ ∈ unitsIn B, nrm s δ ∈ unitsIn B := by
    intro δ hδ
    unfold nrm nrmG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab _ _ hδ
  have hmulU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, nrm s (δ * ε) = nrm s δ * nrm s ε :=
    fun δ hδ ε hε => hmul δ ε (fun t u => hcommU _ (hstab t δ hδ) _ (hstab u ε hε))
  let N : unitsIn B →* unitsIn B := MonoidHom.mk' (fun δ => ⟨nrm s δ, hnrm_mem δ δ.2⟩)
    (fun a b => Subtype.ext (hmulU a a.2 b b.2))
  have hfixN : ∀ δ ∈ unitsIn B, galAct F F' n s (nrm s δ) = nrm s δ := by
    intro δ hδ
    have h4 := hcomm4 δ
    rw [hcommU _ (hnrm_mem δ hδ) _ hδ] at h4
    exact mul_left_cancel h4
  let W : Set (unitsIn B) := {x | galAct F F' n s x = x}
  have hRW : (N.range : Set (unitsIn B)) ⊆ W := by
    rintro _ ⟨δ, rfl⟩
    exact hfixN δ δ.2
  have hVW : Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
      = Nat.card W := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨incl F F' n x.1, x.2⟩, (hfix _).2 ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩
    · intro a b h
      have := congrArg (fun y : W => ((y : unitsIn B) : GL (Fin n) F')) h
      exact Subtype.ext (hinj this)
    · rintro ⟨⟨x, hx⟩, hxW⟩
      obtain ⟨y, rfl⟩ := (hfix x).1 hxW
      exact ⟨⟨y, hx⟩, rfl⟩
  have hUc : Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card (unitsIn B) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hKc : Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
      = Nat.card N.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, (MonoidHom.mem_ker).2 (Subtype.ext ε.2.2)⟩
        invFun := fun ε => ⟨ε.1.1, ε.1.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 ε.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsplit : Nat.card N.ker * Nat.card N.range = Nat.card (unitsIn B) := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hKpos : 0 < Nat.card N.ker := Nat.card_pos
  have hVR : Nat.card W = Nat.card N.range := by
    rw [← hVW]
    rw [hKc, hUc, ← hsplit] at hcard
    exact Nat.eq_of_mul_eq_mul_left hKpos hcard
  have hEq : (N.range : Set (unitsIn B)) = W := by
    apply Set.eq_of_subset_of_ncard_le hRW
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hVR]; rfl
  have hmem : (⟨incl F F' n γ, Algebra.subset_adjoin rfl⟩ : unitsIn B) ∈ W := by
    show galAct F F' n s (incl F F' n γ) = incl F F' n γ
    exact (hfix _).2 ⟨γ, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨δ, hδ⟩ := hmem
  exact ⟨δ, δ.2, congrArg Subtype.val hδ⟩

end GlobalTheory.Shin.NormSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosureStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_base_separable_point_integralClosure : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (exact GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (intros; apply GlobalTheory.KeyOriginEnlargePoint.enlarge_point  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteTypeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlat_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  first | (exact @GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (exact GlobalTheory.EtC.etFF_filtered_colimit_finiteType) | (intros; apply GlobalTheory.EtC.etFF_filtered_colimit_finiteType  <;> assumption)
end

