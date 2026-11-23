module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.PlacesAboveInertOrSplit

open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (D : Dat F E) (v : P F) (w : P E) [hl : w.asIdeal.LiesOver v.asIdeal]

local notation "ι" => completionMap v w
local notation "θw" => algebraMap E (Kv w) D.θ

private theorem pow1 {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one' h1 hn).ne
  · exact h1
  · exact absurd h (one_lt_pow' h1 hn).ne'

private theorem e_ne : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 :=
  (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'

private theorem theta_unit (hd : Valued.v (algebraMap F (Kv v) D.δ) = 1) : Valued.v θw = 1 := by
  have hδ : ι (algebraMap F (Kv v) D.δ) = θw ^ 2 := by
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w), ← D.sq, map_pow]
  have h := congrArg Valued.v hδ
  rw [valued_completionMap, hd, one_pow, map_pow] at h
  exact pow1 two_ne_zero h.symm

private theorem c_add (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (c : Kv v) (hc : Valued.v (ι c) ≤ 1) : Valued.v (ι c + θw) = 1 := by
  have hle : Valued.v (ι c + θw) ≤ 1 :=
    (Valuation.map_add _ _ _).trans (max_le hc hθ.le)
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hc1 : Valued.v (ι c) = 1 := by
    refine le_antisymm hc (not_lt.1 fun h => ?_)
    have : Valued.v (ι c) < Valued.v θw := by rw [hθ]; exact h
    rw [add_comm, Valuation.map_add_eq_of_lt_left _ this, hθ] at hlt
    exact lt_irrefl _ hlt
  have hc2 : Valued.v c = 1 := by
    rw [valued_completionMap] at hc1
    exact pow1 (e_ne (F := F) w) hc1
  let δ := algebraMap F (Kv v) D.δ
  have hδ : ι δ = θw ^ 2 := by
    dsimp [δ]
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv w), ← D.sq, map_pow]
  have hnear : Valued.v (δ - c ^ 2) < 1 := by
    have h3 : Valued.v (ι (δ - c ^ 2)) < 1 := by
      rw [map_sub, hδ, map_pow,
        show θw ^ 2 - ι c ^ 2 = (ι c + θw) * (θw - ι c) by ring, map_mul]
      exact mul_lt_one_of_lt_of_le hlt ((Valuation.map_sub _ _ _).trans (max_le hθ.le hc))
    rw [valued_completionMap] at h3
    by_contra hn
    exact absurd h3 (not_lt.2 (one_le_pow_of_one_le' (not_lt.1 hn) _))
  have hsquare : IsSquare δ := by
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers F v
    have h20 : (2 : Kv v) ≠ 0 := fun h => by simp [h] at h2
    have hc0 : c ≠ 0 := fun h => by simp [h] at hc2
    let z : Kv v := (δ - c ^ 2) / (4 * c ^ 2)
    have h4 : Valued.v (4 * c ^ 2 : Kv v) = 1 := by
      rw [show (4 : Kv v) = 2 * 2 by norm_num, map_mul, map_mul, map_pow, h2, hc2]
      simp
    have hz : Valued.v z < 1 := by
      dsimp [z]
      rwa [map_div₀, h4, div_one]
    let zo : v.adicCompletionIntegers F :=
      ⟨z, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hz.le⟩
    have hzm : zo ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hz.ne
    obtain ⟨s, hs⟩ := GlobalTheory.HenselSquare.exists_sq_add_eq _ _ hzm
    have hs' : (s : Kv v) ^ 2 + s = z := congrArg Subtype.val hs
    refine ⟨c * (1 + 2 * s), ?_⟩
    have hdz : δ = c ^ 2 + z * (4 * c ^ 2) := by
      dsimp [z]
      field_simp
      ring
    rw [hdz, ← hs']
    ring
  have hquad : GlobalTheory.QNorm.IsQuad D.δ D.θ D.σ := by
    refine ⟨?_, D.sq, D.conj, ?_⟩
    · rintro ⟨s, hs⟩
      have hprod : (D.θ - algebraMap F E s) * (D.θ + algebraMap F E s) = 0 := by
        have hsq := D.sq
        rw [hs, map_mul] at hsq
        linear_combination hsq
      have hind := D.b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hind
      rcases mul_eq_zero.1 hprod with h | h
      · have := hind ![-s, 1] (by
          simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
          linear_combination h) 1
        simp at this
      · have := hind ![s, 1] (by
          simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
          linear_combination h) 1
        simp at this
    · intro x
      refine ⟨D.b.repr x 0, D.b.repr x 1, ?_⟩
      conv_lhs => rw [← D.b.sum_repr x]
      simp [Fin.sum_univ_two, D.b0, D.b1, Algebra.smul_def]
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.QNorm.two_places_of_isSquare F E D.δ D.θ D.σ hquad v hsquare
  exact hab ((hu a ((below_eq_iff a v).1 ha)).trans (hu b ((below_eq_iff b v).1 hb)).symm)

private theorem coord (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (u t : Kv v) : Valued.v (ι u + ι t * θw) = max (Valued.v (ι u)) (Valued.v (ι t)) := by
  by_cases ht : t = 0
  · subst ht; simp
  by_cases hut : Valued.v (ι u) ≤ Valued.v (ι t)
  · have h1 : Valued.v (ι (u / t)) ≤ 1 := by
      rw [map_div₀, map_div₀]; exact div_le_one_of_le₀ hut zero_le
    have h3 := c_add D v w h2 hθ hu (u / t) h1
    have h4 : ι u + ι t * θw = ι t * (ι (u / t) + θw) := by
      rw [mul_add, ← map_mul, show t * (u / t) = u by field_simp]
    rw [h4, map_mul, h3, mul_one, max_eq_right hut]
  · have hlt : Valued.v (ι t) < Valued.v (ι u) := not_le.1 hut
    have h5 : Valued.v (ι t * θw) < Valued.v (ι u) := by
      rw [map_mul, hθ, mul_one]; exact hlt
    rw [Valuation.map_add_eq_of_lt_left _ h5, max_eq_left hlt.le]

private theorem e_one (h2 : Valued.v (2 : Kv v) = 1)
    (hθ : Valued.v θw = 1) (hu : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (hef : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 2) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hval := coord D v w h2 hθ hu
  have hr : Module.finrank (Kv v) (Kv w) = 2 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg, hef]
  haveI : Module.Finite (Kv v) (Kv w) := Module.finite_of_finrank_pos (by omega)
  let L : (Kv v × Kv v) →ₗ[Kv v] Kv w :=
    { toFun := fun p => ι p.1 + ι p.2 * θw
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
      map_smul' := fun c p => by
        change ι (c * p.1) + ι (c * p.2) * θw = c • (ι p.1 + ι p.2 * θw)
        rw [Algebra.smul_def, algebraMap_completion_eq, map_mul, map_mul]
        ring }
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun p hp => ?_
    have h := hval p.1 p.2
    rw [show ι p.1 + ι p.2 * θw = 0 from hp, map_zero] at h
    have h1 : Valued.v (ι p.1) = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le
    have h3 : Valued.v (ι p.2) = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le
    exact Prod.ext ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h1))
      ((map_eq_zero ι).1 ((Valuation.zero_iff _).1 h3))
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_prod, Module.finrank_self, hr])).1 hinj
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  obtain ⟨p, hp⟩ := hsurj (algebraMap E (Kv w) π)
  have h := hval p.1 p.2
  rw [show ι p.1 + ι p.2 * θw = algebraMap E (Kv w) π from hp, valued_algebraMap_field, hπ] at h
  obtain ⟨x, hx⟩ : ∃ x : Kv v, WithZero.exp (-1 : ℤ) = Valued.v (ι x) := by
    rcases max_choice (Valued.v (ι p.1)) (Valued.v (ι p.2)) with h' | h'
    · exact ⟨_, h.trans h'⟩
    · exact ⟨_, h.trans h'⟩
  rw [valued_completionMap] at hx
  have he0 := e_ne (F := F) w
  have hx0 : Valued.v x ≠ 0 := fun h0 => by
    rw [h0, zero_pow he0] at hx
    exact WithZero.exp_ne_zero hx
  rw [← WithZero.exp_log hx0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hx
  have hd : ((w.asIdeal.ramificationIdx (𝓞 F) : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) :=
    ⟨-WithZero.log (Valued.v x), by rw [mul_neg, ← hx]; simp⟩
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 hd)

omit hl in
private theorem under_iff : w.under (𝓞 F) = v ↔ w.asIdeal.LiesOver v.asIdeal :=
  ⟨fun h => ⟨by rw [← h]; rfl⟩, fun h => HeightOneSpectrum.ext h.over.symm⟩

omit hl in
private theorem main (hg : Gd D.δ v) :
    (∃ w : P E, w.under (𝓞 F) = v ∧ Inert D v w) ∨
      (∃ w w' : P E, w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v ∧ SplitAt v w ∧ SplitAt v w' ∧
        ∀ w'' : P E, w''.under (𝓞 F) = v → w'' = w ∨ w'' = w') := by
  have hdegree : Module.finrank F E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  have hnorm (w : P E) [hw : w.asIdeal.LiesOver v.asIdeal] :
      normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 F) := by
    have e : v = below F w := ((below_eq_iff w v).2 hw).symm
    subst e
    have := w.isMaximal
    have := (below F w).isMaximal
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal,
      Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (below F w).asIdeal, map_pow]
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  rw [hdegree] at hs
  set g : PlacesOver E v → ℕ := fun x => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) with hg'
  have hs' : ∑ x, g x = 2 := hs
  have hpos : ∀ x, 1 ≤ g x := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hne : Nonempty (PlacesOver E v) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs'
  obtain ⟨a⟩ := hne
  by_cases hu : ∀ b : PlacesOver E v, b = a
  · left
    haveI := a.2
    have h2 : g a = 2 := by
      rw [← hs', Finset.sum_eq_single a (fun b _ hb => absurd (hu b) hb) (fun h => absurd (Finset.mem_univ _) h)]
    have hu' : ∀ w' : P E, w'.asIdeal.LiesOver v.asIdeal → w' = a.1 := fun w' hw' =>
      congrArg Subtype.val (hu ⟨w', hw'⟩)
    have hθ := theta_unit D v a.1 hg.del
    have he := e_one D v a.1 hg.two hθ hu' h2
    have hf : a.1.asIdeal.inertiaDeg (𝓞 F) = 2 := by simpa only [hg', he, one_mul] using h2
    refine ⟨a.1, (under_iff v a.1).2 a.2, ?_⟩
    let i := completionMap v a.1
    let θ := algebraMap E (Kv a.1) D.θ
    have hv (x : Kv v) : Valued.v (i x) = Valued.v x := by
      dsimp [i]
      rw [valued_completionMap, he, pow_one]
    have hval (u t : Kv v) : Valued.v (i u + i t * θ) = max (Valued.v u) (Valued.v t) := by
      have h := coord D v a.1 hg.two hθ hu' u t
      change Valued.v (i u + i t * θ) = max (Valued.v (i u)) (Valued.v (i t)) at h
      rwa [hv, hv] at h
    have hδ : i (algebraMap F (Kv v) D.δ) = θ ^ 2 := by
      dsimp [i, θ]
      rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv a.1), ← D.sq, map_pow]
    have haniso : Aniso D.δ v := by
      intro u t
      rw [← hv, map_sub, map_pow, map_mul, hδ, map_pow,
        show i u ^ 2 - θ ^ 2 * i t ^ 2 = (i u + i t * θ) * (i u + i (-t) * θ) by
          rw [map_neg]
          ring,
        map_mul, hval, hval, Valuation.map_neg, sq]
    obtain ⟨hadd, hmul, hcp, hidl, -, -, -, hsg, -, -⟩ := sgLaws E a.1
    obtain ⟨-, -, hcp', hidl', -, -, -, hsg', -, -⟩ := sgLaws F v
    have hmap (x : Kv v) : adeleMap F E (sg v x) = sg a.1 (i x) := by
      refine Prod.ext ?_ (FiniteAdeleRing.ext E fun w' => ?_)
      · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg a.1 _).1
        rw [(hsg' x).1, (hsg _).1, map_zero]
      · change completionMap (below F w') w' ((sg v x).2 (below F w')) = (sg a.1 _).2 w'
        by_cases h : w' = a.1
        · subst w'
          have hb : below F a.1 = v := (below_eq_iff _ _).2 a.2
          rw [completionMap_congr hb a.1 (sg v x).2]
          exact (congrArg i (hcp' x)).trans (hcp _).symm
        · have hb : below F w' ≠ v := fun hb => h (hu' w' ((below_eq_iff _ _).1 hb))
          rw [(hsg' x).2 _ hb, map_zero, (hsg _).2 _ h]
    have hr : Module.finrank (Kv v) (Kv a.1) = 2 := by
      rw [finrank_eq_ramificationIdx_mul_inertiaDeg, he, hf, one_mul]
    haveI : Module.Finite (Kv v) (Kv a.1) := Module.finite_of_finrank_pos (by omega)
    let L : (Kv v × Kv v) →ₗ[Kv v] Kv a.1 :=
      { toFun := fun p => i p.1 + i p.2 * θ
        map_add' := fun p q => by
          simp only [Prod.fst_add, Prod.snd_add, map_add (f := i)]
          ring
        map_smul' := fun c p => by
          change i (c * p.1) + i (c * p.2) * θ = c • (i p.1 + i p.2 * θ)
          rw [Algebra.smul_def, algebraMap_completion_eq, map_mul, map_mul]
          change i c * i p.1 + i c * i p.2 * θ = i c * (i p.1 + i p.2 * θ)
          ring }
    have hinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun p hp => ?_
      have h := hval p.1 p.2
      rw [show i p.1 + i p.2 * θ = 0 from hp, map_zero] at h
      have h1 : Valued.v p.1 = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le
      have h2 : Valued.v p.2 = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le
      exact Prod.ext ((Valuation.zero_iff _).1 h1) ((Valuation.zero_iff _).1 h2)
    have hsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Module.finrank_prod, Module.finrank_self, hr])).1 hinj
    have hmk (u t : A F) : D.mkE u t = adeleMap F E u + adeleMap F E t * rt D.θ := rfl
    refine ⟨by rw [hnorm a.1, hf], haniso,
      ⟨AddEquiv.ofBijective L.toAddMonoidHom ⟨hinj, hsurj⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro u t
      change sg a.1 (i u + i t * θ) = _
      rw [hmk, hmap, hmap, hadd, mul_comm (sg a.1 (i t)), hmul, mul_comm]
      rfl
    · exact hval
    · intro c u t
      change (i c + i 0 * θ) * (i u + i t * θ) = i (c * u) + i (c * t) * θ
      simp only [map_zero, zero_mul, add_zero, map_mul]
      ring
    · change i 1 + i 0 * θ = 1
      simp
    · intro ϖ hϖ
      let ϖ' : (Kv a.1)ˣ := Units.map (i : Kv v →* Kv a.1) ϖ
      have hco : ((idl a.1 ϖ' : (A E)ˣ) : A E) = adeleMap F E (idl v ϖ : (A F)ˣ).val := by
        rw [hidl, hidl', map_add (f := _), map_one, hmap, map_sub, map_one]
        rfl
      refine ⟨ϖ', ?_, ?_, ?_⟩
      · change Valued.v (i (ϖ : Kv v)) = _
        rw [hv]
        exact hϖ
      · rw [hco, hmk, map_zero, zero_mul, add_zero]
      · have h : idl a.1 ϖ' = ideleEmbedding F E (idl v ϖ) := Units.ext hco
        rw [h, ideleNorm_ideleEmbedding, hdegree]
  · right
    obtain ⟨b, hb⟩ := not_forall.1 hu
    have h1 : g b + g a ≤ 2 := by
      rw [← hs', ← Finset.sum_pair hb]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have ha1 := hpos a
    have hb1 := hpos b
    have hsp : ∀ x : PlacesOver E v, g x = 1 → SplitAt v x.1 := fun x hx => by
      haveI := x.2
      have he := Nat.eq_one_of_mul_eq_one_right hx
      have hf := Nat.eq_one_of_mul_eq_one_left hx
      have hr : Module.finrank (Kv v) (Kv x.1) = 1 := by
        rw [finrank_eq_ramificationIdx_mul_inertiaDeg]
        exact hx
      let i := completionMap v x.1
      have hsurj : Function.Surjective i := fun y => by
        obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (1 : Kv x.1) one_ne_zero).1 hr y
        exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]; rfl⟩
      refine ⟨by rw [hnorm x.1, hf, pow_one], RingEquiv.ofBijective i ⟨i.injective, hsurj⟩,
        continuous_completionMap v x.1, fun y => ?_, fun y => ?_⟩
      · change completionMap v x.1 _ = _
        rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (Kv x.1)]
      · change Valued.v (completionMap v x.1 y) = Valued.v y
        rw [valued_completionMap, he, pow_one]
    refine ⟨b.1, a.1, fun h => hb (Subtype.ext h), (under_iff v b.1).2 b.2, (under_iff v a.1).2 a.2,
      hsp b (by omega), hsp a (by omega), fun w'' hw => ?_⟩
    by_contra hn
    rw [not_or] at hn
    let c : PlacesOver E v := ⟨w'', (under_iff v w'').1 hw⟩
    have hcb : c ≠ b := fun h => hn.1 (congrArg Subtype.val h)
    have hca : c ≠ a := fun h => hn.2 (congrArg Subtype.val h)
    have h3 : g c + (g b + g a) ≤ 2 := by
      rw [← hs', ← Finset.sum_pair hb, ← Finset.sum_insert (by simp [hcb, hca])]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hpos c
    omega

end UpperTheory.PlacesAboveInertOrSplit

theorem UpperTheory.inert_or_split_of_good_delta_rat :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ), H.Gd D.δ v →
          (∃ w : H.P E, w.under (𝓞 ℚ) = v ∧ H.Inert D v w) ∨
          (∃ w w' : H.P E, w ≠ w' ∧ w.under (𝓞 ℚ) = v ∧ w'.under (𝓞 ℚ) = v ∧ H.SplitAt v w ∧ H.SplitAt v w' ∧
            ∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') := by
  intro E _ _ D v hg
  exact UpperTheory.PlacesAboveInertOrSplit.main D v hg
