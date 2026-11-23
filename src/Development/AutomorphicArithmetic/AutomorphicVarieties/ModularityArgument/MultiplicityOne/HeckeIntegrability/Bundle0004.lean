module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PAbsCoreA
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.ACA

section
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private lemma lift_commute_of {X : Type} (u : X → Module.End ℂ Y) (z : Module.End ℂ Y)
    (h : ∀ x, Commute (u x) z) (p : FreeAlgebra ℂ X) : Commute (FreeAlgebra.lift ℂ u p) z := by
  induction p using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Algebra.commutes r z
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul]; exact hp.mul_left hq
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq

private lemma lift_commute {X X' : Type} (u : X → Module.End ℂ Y) (v : X' → Module.End ℂ Y)
    (h : ∀ x y, Commute (u x) (v y)) (p : FreeAlgebra ℂ X) (q : FreeAlgebra ℂ X') :
    Commute (FreeAlgebra.lift ℂ u p) (FreeAlgebra.lift ℂ v q) :=
  lift_commute_of u _ (fun x => (lift_commute_of v (u x) (fun y => (h x y).symm) q).symm) p

private lemma lift_intertwine {X : Type} (u v : X → Module.End ℂ Y) (A : Module.End ℂ Y)
    (h : ∀ x, A * u x = v x * A) (p : FreeAlgebra ℂ X) :
    A * FreeAlgebra.lift ℂ u p = FreeAlgebra.lift ℂ v p * A := by
  induction p using FreeAlgebra.induction with
  | grade0 r => simpa using (Algebra.commutes r A).symm
  | grade1 x => simpa using h x
  | mul p q hp hq => rw [map_mul, map_mul, ← mul_assoc, hp, mul_assoc, hq, mul_assoc]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, add_mul, hp, hq]

private lemma lift_lift {X : Type} (u : X → Module.End ℂ Y) (p : FreeAlgebra ℂ (FreeAlgebra ℂ X)) :
    FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) p =
      FreeAlgebra.lift ℂ u (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q) p) := by
  have h : FreeAlgebra.lift ℂ (fun q => FreeAlgebra.lift ℂ u q) =
      (FreeAlgebra.lift ℂ u).comp (FreeAlgebra.lift ℂ (fun q : FreeAlgebra ℂ X => q)) :=
    FreeAlgebra.hom_ext (by funext q; simp)
  exact DFunLike.congr_fun h p

private lemma mem_adjoin_iff {X : Type} (u : X → Module.End ℂ Y) (x : Module.End ℂ Y) :
    x ∈ Algebra.adjoin ℂ (Set.range u) ↔ ∃ q, FreeAlgebra.lift ℂ u q = x := by
  constructor
  · intro hx
    have hle : Algebra.adjoin ℂ (Set.range u) ≤ (FreeAlgebra.lift ℂ u).range :=
      Algebra.adjoin_le (by
        rintro _ ⟨t, rfl⟩
        exact ⟨FreeAlgebra.ι ℂ t, by simp⟩)
    obtain ⟨q, hq⟩ := hle hx
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    induction q using FreeAlgebra.induction with
    | grade0 r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | grade1 t =>
      simpa using (Algebra.subset_adjoin (Set.mem_range_self t) : u t ∈ Algebra.adjoin ℂ (Set.range u))
    | mul p q hp hq => rw [map_mul]; exact Subalgebra.mul_mem _ hp hq
    | add p q hp hq => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hp hq

private lemma conj_mul (A x y : Module.End ℂ Y) (hAA : A * A = 1) :
    A * x * A * (A * y * A) = A * (x * y) * A := by
  calc A * x * A * (A * y * A) = A * x * (A * A) * y * A := by simp only [mul_assoc]
    _ = A * (x * y) * A := by rw [hAA, mul_one]; simp only [mul_assoc]

end

end UpperTheory.V.Z.Mult.Pi.ACA

open UpperTheory.V.Z.Mult.Pi.ACA in
theorem UpperTheory.V.Z.Mult.Pi.absCoreA_pf :
    AbsCore → RankOne → Corner → MinIdem → AbsCoreA := by
  intro hC hR hK hI I _ J M _ _ _ Y _ _ _ _ α a b A hM hrel haa hab hAA hAb hY
  classical
  obtain ⟨d, hd0, hd⟩ := hC I (fun i => FreeAlgebra ℂ (J i)) M Y
    (fun i q => FreeAlgebra.lift ℂ (α i) q) (fun i q => FreeAlgebra.lift ℂ (a i) q)
    (fun i q => FreeAlgebra.lift ℂ (b i) q) A
    (fun i W hW => hM i W fun f x hx => by simpa using hW (FreeAlgebra.ι ℂ f) x hx)
    (fun i p h => by
      rw [lift_lift] at h ⊢
      exact hrel i _ h)
    (fun i k h f g => lift_commute _ _ (haa i k h) f g)
    (fun i k f g => lift_commute _ _ (hab i k) f g)
    hAA
    (fun i q => lift_intertwine _ _ A (hAb i) q)
    (fun W hW => hY W fun i f x hx => by simpa using hW i (FreeAlgebra.ι ℂ f) x hx)
  have hd' : ∀ x y : ∀ i, FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map fun i =>
        FreeAlgebra.lift ℂ (a i) (x i) * FreeAlgebra.lift ℂ (b i) (y i)).prod * A) =
      d * ∏ i, LinearMap.trace ℂ (M i)
        (FreeAlgebra.lift ℂ (α i) (x i) * FreeAlgebra.lift ℂ (α i) (y i)) := hd
  have hnt : ∀ i, Nontrivial (M i) := by
    intro i
    by_contra hn
    have hs : Subsingleton (M i) := not_nontrivial_iff_subsingleton.1 hn
    have h0 : FreeAlgebra.lift ℂ (α i) (1 : FreeAlgebra ℂ (J i)) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have h1 := hrel i 1 h0
    rw [map_one] at h1
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    exact hy (by simpa using LinearMap.congr_fun h1 y)
  have hex : ∀ i, ∃ p : FreeAlgebra ℂ (J i),
      LinearMap.trace ℂ (M i) (FreeAlgebra.lift ℂ (α i) p * FreeAlgebra.lift ℂ (α i) p) = 1 ∧
      FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) p = FreeAlgebra.lift ℂ (a i) p ∧
      ∀ q, ∃ c : ℂ, FreeAlgebra.lift ℂ (a i) p * FreeAlgebra.lift ℂ (a i) q *
        FreeAlgebra.lift ℂ (a i) p = c • FreeAlgebra.lift ℂ (a i) p := fun i => by
    haveI := hnt i
    exact hI (J i) (M i) Y (α i) (a i) (hM i) (hrel i)
  choose p hp1 hp2 hp3 using hex
  have hAq : ∀ i q, A * FreeAlgebra.lift ℂ (a i) q = FreeAlgebra.lift ℂ (b i) q * A :=
    fun i q => lift_intertwine _ _ A (hAb i) q
  have hbq : ∀ i q, FreeAlgebra.lift ℂ (b i) q = A * FreeAlgebra.lift ℂ (a i) q * A :=
    fun i q => by rw [hAq, mul_assoc, hAA, mul_one]
  have hbf : ∀ i f, b i f = A * a i f * A := fun i f => by rw [hAb, mul_assoc, hAA, mul_one]
  have hbb : ∀ i k, i ≠ k → ∀ f g, Commute (b i f) (b k g) := by
    intro i k h f g
    show b i f * b k g = b k g * b i f
    rw [hbf i f, hbf k g, conj_mul A _ _ hAA, conj_mul A _ _ hAA, (haa i k h f g).eq]
  obtain ⟨e, he⟩ : ∃ e : I → Module.End ℂ Y, ∀ i, e i = FreeAlgebra.lift ℂ (a i) (p i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : I → Module.End ℂ Y, ∀ i, e' i = FreeAlgebra.lift ℂ (b i) (p i) :=
    ⟨_, fun _ => rfl⟩
  have hee' : ∀ i, e' i = A * e i * A := fun i => by rw [he, he', hbq]
  have hidem : ∀ i, e i * e i = e i := fun i => by rw [he]; exact hp2 i
  have hcorner := hK I J Y a b e e' haa hab hbb hY
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he i).symm⟩, hidem i, fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      rw [he]
      exact hp3 i q⟩)
    (fun i => ⟨(mem_adjoin_iff _ _).2 ⟨p i, (he' i).symm⟩, by
        rw [hee', conj_mul A _ _ hAA, hidem], fun x hx => by
      obtain ⟨q, rfl⟩ := (mem_adjoin_iff _ _).1 hx
      obtain ⟨c, hc⟩ := hp3 i q
      refine ⟨c, ?_⟩
      rw [hee', hbq, conj_mul A _ _ hAA, conj_mul A _ _ hAA, he, hc, mul_smul_comm, smul_mul_assoc]⟩)
    _ rfl
  obtain ⟨hff, hsc⟩ := hcorner
  have hfac : ∀ i, Commute A (e i * e' i) := by
    intro i
    have hce : Commute (e i) (e' i) := by
      rw [he, he']
      exact lift_commute _ _ (hab i i) _ _
    have h1 : A * e i = e' i * A := by rw [he, he']; exact hAq i (p i)
    have h2 : A * e' i = e i * A := by
      rw [hee', ← mul_assoc, ← mul_assoc, hAA, one_mul]
    show A * (e i * e' i) = e i * e' i * A
    calc A * (e i * e' i) = A * e i * e' i := by rw [mul_assoc]
      _ = e' i * (A * e' i) := by rw [h1, mul_assoc]
      _ = e' i * e i * A := by rw [h2, mul_assoc]
      _ = e i * e' i * A := by rw [hce.eq]
  have hAF : Commute A ((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod :=
    Commute.list_prod_right _ _ (by
      intro z hz
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hz
      exact hfac k)
  have htr : LinearMap.trace ℂ Y
      (((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod * A) = d := by
    have h := hd' p p
    simp only [hp1, Finset.prod_const_one, mul_one] at h
    simpa only [he, he'] using h
  have hn : ‖d‖ = 1 := by
    rcases hR Y _ A hff hAA hAF.eq hsc with h | h
    · rw [htr] at h
      exact absurd h hd0
    · rwa [htr] at h
  refine ⟨d, hn, fun f g => ?_⟩
  simpa using hd' (fun i => FreeAlgebra.ι ℂ (f i)) (fun i => FreeAlgebra.ι ℂ (g i))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PCorner
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi.Cn

variable {R : Type} [Ring R] [Algebra ℂ R]

private def Good (s : Set R) (e : R) : Prop :=
  e ∈ Algebra.adjoin ℂ s ∧ e * e = e ∧ ∀ x ∈ Algebra.adjoin ℂ s, ∃ c : ℂ, e * x * e = c • e

private lemma adj_comm {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : R}
    (hx : x ∈ Algebra.adjoin ℂ s) (hy : y ∈ Algebra.adjoin ℂ t) : Commute x y :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun _ hb =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => (h a ha _ hb).symm).symm

private lemma mem_span {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {z : R}
    (hz : z ∈ Algebra.adjoin ℂ (s ∪ t)) :
    z ∈ Submodule.span ℂ {w : R | ∃ x ∈ Algebra.adjoin ℂ s, ∃ y ∈ Algebra.adjoin ℂ t, w = x * y} := by
  induction hz using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · exact Submodule.subset_span ⟨g, Algebra.subset_adjoin hg, 1, one_mem _, (mul_one _).symm⟩
    · exact Submodule.subset_span ⟨1, one_mem _, g, Algebra.subset_adjoin hg, (one_mul _).symm⟩
  | algebraMap r =>
    exact Submodule.subset_span ⟨_, Subalgebra.algebraMap_mem _ r, 1, one_mem _, (mul_one _).symm⟩
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv =>
    have hm := Submodule.mul_mem_mul hu hv
    rw [Submodule.span_mul_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, _, ⟨x', hx', y', hy', rfl⟩, rfl⟩
    refine ⟨x * x', mul_mem hx hx', y * y', mul_mem hy hy', ?_⟩
    exact ((adj_comm h hx' hy).mul_mul_mul_comm x y').symm

private lemma good_two {s t : Set R} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {e e' : R}
    (he : Good s e) (he' : Good t e') : Good (s ∪ t) (e * e') := by
  obtain ⟨m, i, c⟩ := he
  obtain ⟨m', i', c'⟩ := he'
  refine ⟨mul_mem (Algebra.adjoin_mono Set.subset_union_left m)
    (Algebra.adjoin_mono Set.subset_union_right m'), ?_, fun z hz => ?_⟩
  · rw [(adj_comm h m m').symm.mul_mul_mul_comm, i, i']
  · have hz' := mem_span h hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      obtain ⟨p, hp⟩ := c x hx
      obtain ⟨q, hq⟩ := c' y hy
      refine ⟨p * q, ?_⟩
      rw [(adj_comm h hx m').symm.mul_mul_mul_comm,
        (adj_comm h m (mul_mem m' hy)).symm.mul_mul_mul_comm, hp, hq, smul_mul_smul_comm]
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨p, hp⟩ := hu
      obtain ⟨q, hq⟩ := hv
      exact ⟨p + q, by rw [mul_add, add_mul, hp, hq, add_smul]⟩
    | smul r u _ hu =>
      obtain ⟨p, hp⟩ := hu
      exact ⟨r * p, by rw [mul_smul_comm, smul_mul_assoc, hp, smul_smul]⟩

private lemma good_list {I : Type} (s : I → Set R) (e : I → R)
    (h : ∀ i k, i ≠ k → ∀ x ∈ s i, ∀ y ∈ s k, Commute x y) (he : ∀ i, Good (s i) (e i))
    (l : List I) (hl : l.Nodup) : Good {x | ∃ i ∈ l, x ∈ s i} (l.map e).prod := by
  induction l with
  | nil =>
    refine ⟨by simpa using one_mem _, by simp, fun x hx => ?_⟩
    have h0 : {x | ∃ i ∈ ([] : List I), x ∈ s i} = ∅ := by simp
    rw [h0, Algebra.adjoin_empty, Algebra.mem_bot] at hx
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, by simp [Algebra.algebraMap_eq_smul_one]⟩
  | cons i l ih =>
    have hn := List.nodup_cons.1 hl
    have h0 : {x | ∃ k ∈ i :: l, x ∈ s k} = s i ∪ {x | ∃ k ∈ l, x ∈ s k} := by
      ext x; simp
    rw [h0, List.map_cons, List.prod_cons]
    refine good_two ?_ (he i) (ih hn.2)
    rintro x hx y ⟨k, hk, hy⟩
    exact h i k (fun e => hn.1 (e ▸ hk)) x hx y hy

end UpperTheory.V.Z.Mult.Pi.Cn

open UpperTheory.V.Z.Mult.Pi.Cn in
theorem UpperTheory.V.Z.Mult.Pi.corner_pf :
    Corner := by
  intro I _ J Y _ _ _ _ a b e e' haa hab hbb hY he he' f hf
  have hg := good_list (fun i => Set.range (a i) ∪ Set.range (b i)) (fun i => e i * e' i)
    (by
      rintro i k hik x (⟨p, rfl⟩ | ⟨p, rfl⟩) y (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · exact haa i k hik p q
      · exact hab i k p q
      · exact (hab k i q p).symm
      · exact hbb i k hik p q)
    (fun i => good_two (by
      rintro x ⟨p, rfl⟩ y ⟨q, rfl⟩
      exact hab i i p q) (he i) (he' i))
    (Finset.univ : Finset I).toList (Finset.nodup_toList _)
  rw [← hf] at hg
  obtain ⟨-, h1, h2⟩ := hg
  refine ⟨h1, fun x => ?_⟩
  have hsurj := DiscreteGroups.T1.Desc.Swap3.burnside (Algebra.adjoin ℂ
    {x | ∃ i ∈ (Finset.univ : Finset I).toList, x ∈ Set.range (a i) ∪ Set.range (b i)}).val (by
    intro W hW
    refine hY W fun i p x hx => ⟨?_, ?_⟩
    · exact hW ⟨a i p, Algebra.subset_adjoin ⟨i, by simp, Or.inl ⟨p, rfl⟩⟩⟩ x hx
    · exact hW ⟨b i p, Algebra.subset_adjoin ⟨i, by simp, Or.inr ⟨p, rfl⟩⟩⟩ x hx)
  obtain ⟨⟨z, hz⟩, rfl⟩ := hsurj x
  exact h2 z hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PLevIdx
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

namespace UpperTheory.V.Z.Mult.Pi

private theorem relIndex_positions {G ι : Type} [Group G] {A : ι → Type} [∀ i, Group (A i)] (K : Subgroup G)
    (q : ∀ i, G →* A i) (j : ∀ i, A i →* G) (B N : ∀ i, Subgroup (A i)) (T : Finset ι)
    (hqj : ∀ i ∈ T, ∀ a, q i (j i a) = a)
    (hqk : ∀ i ∈ T, ∀ k ∈ T, i ≠ k → ∀ a, q k (j i a) = 1)
    (hj : ∀ i ∈ T, ∀ a ∈ B i, j i a ∈ K)
    (hq : ∀ i ∈ T, ∀ k ∈ K, q i k ∈ B i) :
    (K ⊓ ⨅ i ∈ T, (N i).comap (q i)).relIndex K = ∏ i ∈ T, (N i).relIndex (B i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    have ih' := ih (fun k hk => hqj k (Finset.mem_insert_of_mem hk))
      (fun k hk l hl => hqk k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl))
      (fun k hk => hj k (Finset.mem_insert_of_mem hk))
      (fun k hk => hq k (Finset.mem_insert_of_mem hk))
    have hiT : i ∈ insert i T := Finset.mem_insert_self i T
    set L : Subgroup G := K ⊓ ⨅ k ∈ T, (N k).comap (q k) with hL
    have hins : (K ⊓ ⨅ k ∈ insert i T, (N k).comap (q k)) = L ⊓ (N i).comap (q i) := by
      rw [Finset.iInf_insert, inf_left_comm, inf_comm]
    have hmap : L.map (q i) = B i := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hq i hiT x (Subgroup.mem_inf.1 hx).1
      · intro a ha
        refine ⟨j i a, ?_, hqj i hiT a⟩
        refine Subgroup.mem_inf.2 ⟨hj i hiT a ha, ?_⟩
        simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
        intro k hk
        have hne : i ≠ k := fun h => hi (h ▸ hk)
        rw [hqk i hiT k (Finset.mem_insert_of_mem hk) hne a]
        exact (N k).one_mem
    rw [hins, Finset.prod_insert hi, ← ih',
      ← Subgroup.relIndex_mul_relIndex (L ⊓ (N i).comap (q i)) L K inf_le_left inf_le_left,
      Subgroup.inf_relIndex_left, Subgroup.relIndex_comap, hmap]

private theorem mem_Lev {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}
    (S : Set (GlobalTheory.BCT.Pl E)) (N : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (g : GF E n) :
    g ∈ Lev S N ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ N i.1 := by
  unfold Lev
  rw [Subgroup.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.1 i.2⟩

theorem levIdx_pf :
    SlotBasic → LevTop → LevIdx := by
  intro hF _ E _ _ _ n S Z N hS hZ hG
  obtain ⟨-, -, h3, h4, -, -, h7⟩ := hF E n S hS
  have hK : ∀ g, g ∈ PositivityTheory.Rg.BcB.G8.Kf E n ↔ ∀ i, Sl S i → qw n i.1 i.2 g ∈ GlobalTheory.LFun.KGL i.1 (n := n) := fun g => by
    rw [← h7, mem_Lev]
  have hLe : Lev S N ≤ PositivityTheory.Rg.BcB.G8.Kf E n := fun g hg =>
    (hK g).2 fun i hi => (hG i.1).2.1 ((mem_Lev S N g).1 hg i hi)
  refine ⟨hLe, ?_⟩
  have hposition : ∀ i ∈ Z ×ˢ (Finset.univ : Finset Bool), Sl S i := fun i hi => by
    have hw := hZ i.1 (Finset.mem_product.1 hi).1
    exact ⟨hw.1, fun _ => hw.2⟩
  have hEq : Lev S N = PositivityTheory.Rg.BcB.G8.Kf E n ⊓ ⨅ i ∈ Z ×ˢ (Finset.univ : Finset Bool),
      (N i.1).comap (qw n i.1 i.2) := by
    apply le_antisymm
    · intro g hg
      refine Subgroup.mem_inf.2 ⟨hLe hg, ?_⟩
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap]
      exact fun i hi => (mem_Lev S N g).1 hg i (hposition i hi)
    · intro g hgg
      obtain ⟨hg, hg'⟩ := Subgroup.mem_inf.1 hgg
      simp only [Subgroup.mem_iInf, Subgroup.mem_comap] at hg'
      refine (mem_Lev S N g).2 fun i hi => ?_
      by_cases hw : i.1 ∈ Z
      · exact hg' i (Finset.mem_product.2 ⟨hw, Finset.mem_univ _⟩)
      · rw [(hG i.1).2.2.2 hw]
        exact (hK g).1 hg i hi
  have key := relIndex_positions (A := fun i : GlobalTheory.BCT.Pl E × Bool => GlobalTheory.BCT.GLw n i.1) (PositivityTheory.Rg.BcB.G8.Kf E n)
    (fun i => qw n i.1 i.2) (fun i => jw n i.1 i.2) (fun i => GlobalTheory.LFun.KGL i.1 (n := n)) (fun i => N i.1)
    (Z ×ˢ (Finset.univ : Finset Bool))
    (fun i _ a => (h3 i.1 i.2).2.2.1 a)
    (fun i hi k hk hne a => h4 i k (hposition i hi) (hposition k hk) hne a)
    (fun i hi a ha => (hK _).2 fun k hk => by
      by_cases hik : i = k
      · subst hik
        rw [(h3 i.1 i.2).2.2.1 a]
        exact ha
      · rw [h4 i k (hposition i hi) hk hik a]
        exact (GlobalTheory.LFun.KGL k.1 (n := n)).one_mem)
    (fun i hi k hk => (hK k).1 hk i (hposition i hi))
  rw [hEq, key, Finset.prod_product]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp [Fintype.prod_bool, sq]

end UpperTheory.V.Z.Mult.Pi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PMinIdem
section
namespace UpperTheory.V.Z.Mult.Pi

theorem minIdem_pf : MinIdem := by
  intro J M Y _ _ _ _ _ _ α a hs hk
  have surj : Function.Surjective (FreeAlgebra.lift ℂ α) :=
    DiscreteGroups.T1.Desc.Swap3.burnside (FreeAlgebra.lift ℂ α) fun W hW => hs W fun f x hx => by
      simpa using hW (FreeAlgebra.ι ℂ f) x hx
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨p, hp⟩ := surj (LinearMap.smulRight l v)
  have same : ∀ r r', FreeAlgebra.lift ℂ α r = FreeAlgebra.lift ℂ α r' →
      FreeAlgebra.lift ℂ a r = FreeAlgebra.lift ℂ a r' := by
    intro r r' h
    have h0 : FreeAlgebra.lift ℂ a (r - r') = 0 := hk _ (by rw [map_sub, h, sub_self])
    rw [map_sub] at h0
    exact sub_eq_zero.1 h0
  have idem : LinearMap.smulRight l v * LinearMap.smulRight l v = LinearMap.smulRight l v := by
    ext x
    simp [hl]
  refine ⟨p, ?_, ?_, fun q => ⟨l (FreeAlgebra.lift ℂ α q v), ?_⟩⟩
  · rw [hp, idem, LinearMap.trace_smulRight, hl]
  · rw [← map_mul]
    exact same _ _ (by rw [map_mul, hp, idem])
  · rw [← map_mul, ← map_mul, ← map_smul]
    refine same _ _ ?_
    rw [map_mul, map_mul, map_smul, hp]
    ext x
    simp [smul_smul, mul_comm]

end UpperTheory.V.Z.Mult.Pi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PVolIdx
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Mult.Pi

private theorem haar_measure_rel_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : MeasureTheory.Measure Γ) [μ.IsHaarMeasure]
    (K K' : Subgroup Γ) (hK' : IsOpen (K' : Set Γ)) (hK : IsCompact (K : Set Γ)) (hle : K' ≤ K) :
    (μ K').toReal * (K'.relIndex K : ℕ) = (μ K).toReal := by
  classical
  have hopen : ∀ g : Γ, IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K' : Set Γ)) := fun g =>
    hK'.preimage (continuous_const.mul continuous_id)
  have hcov : (K : Set Γ) ⊆ ⋃ k : K, (fun x => (k : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    simp [K'.one_mem]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun k : K => hopen (k : Γ)) hcov
  have hmem : ∀ a b : K, ((a : Γ)⁻¹ * (b : Γ) ∈ K') ↔
      (QuotientGroup.mk a : K ⧸ K'.subgroupOf K) = QuotientGroup.mk b := by
    intro a b
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hfin : Finite (K ⧸ K'.subgroupOf K) := by
    refine Finite.of_surjective
      (fun k : t => (QuotientGroup.mk (k : K) : K ⧸ K'.subgroupOf K)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht x.2)
      exact ⟨⟨k, hk⟩, (hmem k x).1 hx⟩
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let s : K ⧸ K'.subgroupOf K → K := Quotient.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ K'.subgroupOf K) = q := fun q =>
    QuotientGroup.out_eq' q
  let f : K ⧸ K'.subgroupOf K → Set Γ := fun q =>
    (fun x => ((s q : K) : Γ)⁻¹ * x) ⁻¹' (K' : Set Γ)
  have hU : (K : Set Γ) = ⋃ q, f q := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.2 ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      exact (hmem _ ⟨x, hx⟩).2 (hs _)
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hx
      have h1 : ((s q : K) : Γ)⁻¹ * x ∈ K := hle hq
      have h2 := K.mul_mem (s q).2 h1
      simpa using h2
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro p q hpq
    refine Set.disjoint_left.2 ?_
    intro x hp hq
    apply hpq
    have hp' : ((s p : K) : Γ)⁻¹ * x ∈ K' := hp
    have hq' : ((s q : K) : Γ)⁻¹ * x ∈ K' := hq
    have h3 : ((s p : K) : Γ)⁻¹ * (s q : K) ∈ K' := by
      have := K'.mul_mem hp' (K'.inv_mem hq')
      simpa [mul_assoc] using this
    rw [← hs p, ← hs q]
    exact (hmem _ _).1 h3
  have hμ : ∀ q, μ (f q) = μ K' := fun q =>
    MeasureTheory.measure_preimage_mul μ _ _
  have hsum := MeasureTheory.measure_iUnion (μ := μ) hdisj (fun q => (hopen _).measurableSet)
  rw [← hU, tsum_fintype] at hsum
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hsum, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm]
  simp only [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem UpperTheory.V.Z.Mult.Pi.volIdx_pf :
    VolIdx := by
  intro Γ _ _ _ _ _ μ _ K K' hK' hK hle
  exact haar_measure_rel_index μ K K' hK' hK hle
end

