module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToPartFrob
section
noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem bb_eq (p r : ℕ) : BB p r = Formalism.CyclotomicNorms.BB r p := by
  ext l
  simp only [BB, Formalism.CyclotomicNorms.BB, Formalism.CyclotomicNorms.Exc, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, ← pow_mul, mul_comm 4]
  refine or_congr_right ⟨fun ⟨h, a, h1, h2, h3⟩ => ⟨a, h1, h2, h, h3⟩, fun ⟨a, h1, h2, h, h3⟩ => ⟨h, a, h1, h2, h3⟩⟩

theorem primeToPart_frob (l i : ℕ) (z : Fbar p) (a : ZMod p) :
    Formalism.CyclotomicNorms.primeToPart l (z ^ p ^ i) = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) ↔
      Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) := by
  let β : Fbar p ≃* Fbar p := (iterateFrobeniusEquiv (Fbar p) p i).toMulEquiv
  have h1 : z ^ p ^ i = β z := rfl
  have h2 : β (algebraMap (ZMod p) (Fbar p) a) = algebraMap (ZMod p) (Fbar p) a := by
    show algebraMap (ZMod p) (Fbar p) a ^ p ^ i = _
    rw [← map_pow, ZMod.pow_card_pow]
  conv_lhs => rw [h1, ← h2, GlobalTheory.GoodCharsCompare.primeToPart_map, GlobalTheory.GoodCharsCompare.primeToPart_map]
  exact β.injective.eq_iff

section Good

variable {L : GlobalTheory.GLq.LabelDatum p} {r : ℕ} {s : SSParam p ℂ r} {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]}

theorem Labels.root (h : Labels L s x f) (y) : LabelsChar L (rootChar s y) (rootElt x y) :=
  (_root_.GlobalTheory.LabelNorm.main p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 y.1) _ _ _ (h.1 y.1)

theorem Labels.cyc (h : Labels L s x f) (c) : LabelsChar L (cycChar s c) (x c) := by
  have := (_root_.GlobalTheory.LabelNorm.main p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 c) _ _ 1 (h.1 c)
  rwa [pow_one, pow_one] at this

theorem Labels.mem_roots (h : Labels L s x f) (z : Fbar p) : z ∈ Formalism.CyclotomicNorms.rootsBar f ↔ ∃ y, rootElt x y = z := by
  rw [h.2.2.2]; simp

theorem Labels.regular_iff (h : Labels L s x f) : IsRegularParam s ↔ Squarefree f := by
  rw [(_root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor p r _ x f h.2).2.2.1]
  exact forall₂_congr fun y y' => by
    rw [(_root_.GlobalTheory.ParamLabel.Congr.eq_and_congr p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).1]

theorem Labels.two_iff (h : Labels L s x f) (hs : Squarefree f) {l : ℕ} (hl : l.Prime) :
    (∀ y y', y ≠ y' → ¬ CongrMod l (rootChar s y) (rootChar s y')) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, ∀ z' ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l z' → z = z' := by
  have hi := (_root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor p r _ x f h.2).2.2.1.1 hs
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, hi.eq_iff]
  exact forall₂_congr fun y y' => by
    rw [(_root_.GlobalTheory.ParamLabel.Congr.eq_and_congr p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).2 l hl, not_imp_not]

theorem Labels.three_iff (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a)
    {l : ℕ} (hl : l.Prime) :
    (∀ c, ¬ CongrMod l (cycChar s c) (χ.comp (baseNorm p r.factorial))) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have hχ := ((_root_.GlobalTheory.LabelNorm.main p L _ r.factorial_pos).2 χ a ha).1
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, rootElt, Ne, primeToPart_frob,
    (_root_.GlobalTheory.ParamLabel.Congr.eq_and_congr p L _ r.factorial_pos _ _ _ _ (h.cyc _) hχ).2 l hl]
  exact ⟨fun H y => H y.1, fun H c => H ⟨c, ⟨0, cycLen_pos _ c⟩⟩⟩

theorem Labels.ne_of (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a) {l : ℕ}
    (H : ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p))) (y) :
    rootChar s y ≠ χ.comp (baseNorm p r.factorial) := fun e => by
  have hχ := ((_root_.GlobalTheory.LabelNorm.main p L _ r.factorial_pos).2 χ a ha).1
  have := (_root_.GlobalTheory.ParamLabel.Congr.eq_and_congr p L _ r.factorial_pos _ _ _ _ (h.root y) hχ).1.1 e
  exact H _ ((h.mem_roots _).2 ⟨y, rfl⟩) (by rw [this])

theorem Labels.dvd_iff (h : Labels L s x f) (hs : Squarefree f) :
    (∀ a : ℕ, (∃ q : (ZMod p)[X], q ∣ f ∧ q.natDegree = a) ↔ ∃ A : Finset (Cyc s.1), ∑ c ∈ A, cycLen s.1 c = a) ∧
    ∀ Q : ℕ → Prop, (∃ q : (ZMod p)[X], Irreducible q ∧ q ∣ f ∧ Q q.natDegree) ↔ ∃ c, Q (cycLen s.1 c) := by
  obtain ⟨h1, h2, h3⟩ := (_root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor p r _ x f h.2).2.2.2 hs
  have := _root_.GlobalTheory.Div.natDegree_divisors_prod_distinct_monic_irreducible.natDegree_divisors_prod (ZMod p) _ _ (fun c => ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (x c)),
    minpoly.irreducible (Algebra.IsIntegral.isIntegral (x c))⟩) h2
  simp only [h1, ← h3] at this
  exact this

end Good

theorem good_iff (L : GlobalTheory.GLq.LabelDatum p) (h5 : 5 ≤ p) {r : ℕ} {ι J : Type} (s : ι → SSParam p ℂ r)
    (x : ∀ v, Cyc (s v).1 → Fbar p) (f : ι → (ZMod p)[X]) (h : ∀ v, Labels L (s v) (x v) (f v))
    (χ : J → (ZMod p)ˣ →* ℂˣ) (a : ι → J → (ZMod p)ˣ)
    (ha : ∀ v j, LabelsTame L (χ j) (a v j) ∨ LabelsTame L (χ j)⁻¹ (a v j)) :
    GoodAt χ s ↔ Formalism.CyclotomicNorms.IsGood r p f a ∧ Formalism.CyclotomicNorms.IsGood r p f fun v j => (a v j)⁻¹ := by
  have inv : ∀ {χ : (ZMod p)ˣ →* ℂˣ} {a}, LabelsTame L χ a → LabelsTame L χ⁻¹ a⁻¹ := fun h =>
    ((_root_.GlobalTheory.LabelNorm.main p L 1 one_pos).2 _ _ h).2
  have three : ∀ l : ℕ, l.Prime → ∀ v j,
      ((∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial))) ∧
        ∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ↔
      (∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a v j : ZMod p))) ∧
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) ((a v j)⁻¹ : (ZMod p)ˣ)) := by
    intro l hl v j
    rcases ha v j with H | H
    · rw [(h v).three_iff H hl, (h v).three_iff (inv H) hl]
    · have H' := inv H
      rw [inv_inv] at H'
      rw [(h v).three_iff H hl, (h v).three_iff H' hl, and_comm]
  have base := fun v => _root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor p r _ (x v) (f v) (h v).2
  constructor
  · rintro ⟨g1, g2, ⟨g3, -⟩, g4, g5⟩
    have hs := fun v => (h v).regular_iff.1 (g1 v)
    have k3 := fun l hl hp v j => (three l hl v j).1 ⟨fun c => (g3 l hl hp v j c).1, fun c => (g3 l hl hp v j c).2⟩
    have key : ∀ a' : ι → J → (ZMod p)ˣ, (∀ l : ℕ, l.Prime → l ≠ p → ∀ v j, ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v),
        Formalism.CyclotomicNorms.primeToPart l z ≠ Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a' v j : ZMod p))) →
        Formalism.CyclotomicNorms.IsGood r p f a' := fun a' H => by
      refine ⟨fun v => ⟨(h v).2.2.1, (base v).1, (base v).2.1⟩, hs,
        fun l hl hb v => ((h v).two_iff (hs v) hl).1 (g2 l hl (bb_eq p r ▸ hb) v), H, fun n h1 h2 => ?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact g4 ⟨n, h1, h2, fun v => (((h v).dvd_iff (hs v)).1 n).1 (hc v)⟩
      · obtain ⟨v, hv⟩ := g5
        exact ⟨v, (((h v).dvd_iff (hs v)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).2 hv⟩
    exact ⟨key _ fun l hl hp v j => (k3 l hl hp v j).1, key _ fun l hl hp v j => (k3 l hl hp v j).2⟩
  · rintro ⟨⟨-, hs, g2, g3, g4, v₀, g5⟩, -, -, -, g3', -⟩
    have k3 := fun l hl hp v j => (three l hl v j).2 ⟨g3 l hl hp v j, g3' l hl hp v j⟩
    refine ⟨fun v => (h v).regular_iff.2 (hs v), fun l hl hb v => ((h v).two_iff (hs v) hl).2 (g2 l hl (bb_eq p r ▸ hb) v),
      ⟨fun l hl hp v j c => ⟨(k3 l hl hp v j).1 c, (k3 l hl hp v j).2 c⟩, fun v j y => ?_⟩, ?_,
      v₀, (((h v₀).dvd_iff (hs v₀)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).1 g5⟩
    · have e1 := g3 2 Nat.prime_two (by omega) v j
      have e2 := g3' 2 Nat.prime_two (by omega) v j
      rcases ha v j with H | H
      · exact ⟨(h v).ne_of H e1 y, (h v).ne_of (inv H) e2 y⟩
      · have H' := inv H
        rw [inv_inv] at H'
        exact ⟨(h v).ne_of H' e2 y, (h v).ne_of H e1 y⟩
    · rintro ⟨n, h1, h2, H⟩
      obtain ⟨v, hv⟩ := g4 n h1 h2
      exact hv ((((h v).dvd_iff (hs v)).1 n).2 (H v))

theorem Labels.series (hG : GlobalTheory.GLq.Green) {L : GlobalTheory.GLq.LabelDatum p} (h5 : 5 ≤ p) {r : ℕ} {s : SSParam p ℂ r}
    {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]} (h : Labels L s x f) (hs : Squarefree f) :
    {χ | GlobalTheory.GLq.IsIrr χ ∧ GlobalTheory.GLq.HasLabel L χ f} = {typeChar s} ∧
      GlobalTheory.GLq.eSerC L r f = centralIdem (typeChar s) := by
  obtain ⟨d1, d2, -, d3⟩ := _root_.GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor p r _ x f h.2
  obtain ⟨h1, h2, h3⟩ := d3 hs
  obtain ⟨l, hl, hl', e⟩ := _root_.GlobalTheory.TypeCharProduct.typeChar_eq_hcL p r s
  let Q : List ((ZMod p)[X] × GlobalTheory.GLq.Pc p) := l.map fun c => (minpoly (ZMod p) (x c), ⟨cycLen s.1 c, cuspOn (s.2 c)⟩)
  have hsnd : Q.map Prod.snd = l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p) := by
    rw [List.map_map]; rfl
  have hfst : Q.map Prod.fst = l.map fun c => minpoly (ZMod p) (x c) := by
    rw [List.map_map]; rfl
  have hQ : ∀ q ∈ Q, GlobalTheory.GLq.IsCuspOf L q.1 q.2.2 := by
    intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    exact _root_.GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green hG p L h5 _ (s.2 c) (x c) (cycLen_pos _ c) (h.1 c) (h1 c)
  have hprod : f = (Q.map Prod.fst).prod := by
    classical
    rw [hfst, h3, ← List.prod_toFinset _ hl]
    congr 1
    exact (Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (hl' c)).symm
  have hdeg : GlobalTheory.GLq.degL (Q.map Prod.snd) = r := by
    rw [← (GlobalTheory.GLq.Label.prod_props L Q hQ).2.1, ← hprod, d1]
  have hnd : (Q.map Prod.snd).Nodup := by
    apply List.Nodup.of_map (GlobalTheory.GLq.Label.lab L)
    rw [← GlobalTheory.GLq.Label.map_fst_eq L h5 Q hQ, hfst]
    exact hl.map h2
  rw [← hsnd] at e
  have hip := (_root_.GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp p _ _ r hdeg hdeg (GlobalTheory.GLq.Label.cusp_snd L Q hQ) (GlobalTheory.GLq.Label.cusp_snd L Q hQ)).2 hnd
  have hirr : GlobalTheory.GLq.IsIrr (typeChar s) :=
    e ▸ (_root_.GlobalTheory.charDec _ _).2.2.2.1 (_root_.GlobalTheory.gl_list_product_perm_char p _ [] r hdeg.symm (GlobalTheory.GLq.Label.char_snd L Q hQ)).1 hip
  have hlab : GlobalTheory.GLq.HasLabel L (typeChar s) f := ⟨Q, hQ, hdeg, hprod, by rw [e, hip]; exact one_ne_zero⟩
  obtain ⟨Q', -, -, -, hset⟩ := GlobalTheory.GLq.Label.squarefree_series L h5 hG r f h.2.2.1 d1 d2 hs
  have : typeChar s = GlobalTheory.GLq.hcL (Q'.map Prod.snd) r := by
    rw [← Set.mem_singleton_iff, ← hset]; exact ⟨hirr, hlab⟩
  refine ⟨this ▸ hset, ?_⟩
  unfold GlobalTheory.GLq.eSerC
  rw [hset, finsum_mem_singleton, ← this]
  unfold GlobalTheory.GLq.zOf centralIdem
  rw [Nat.card_eq_fintype_card]
  convert rfl

end GlobalTheory.ParamLabel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingWordSpanStableOfLoweringKill
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.raisingSpan_stable : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ L : Submodule ℂ V, KStab ε E L → (∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0) → ∀ (a b : Fin n), ∀ y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x}, E a b y ∈ Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} := by
  intro n ε V _ _ E hG L hK hL
  set S := Submodule.span ℂ {y : V | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have gen : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x ∈ S :=
    fun l hl x hx => Submodule.subset_span ⟨l, hl, x, hx, rfl⟩
  have pre : ∀ c d, ε c = true → ε d = false → ∀ y ∈ S, E c d y ∈ S := by
    intro c d hc hd y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hz
      have h1 := gen ((c, d) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hc, hd⟩
        · exact hl p hp) x hx
      simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using h1
    | zero => rw [map_zero]; exact S.zero_mem
    | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
  have main : ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) → ∀ x ∈ L,
      ∀ a b, E a b ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod x) ∈ S := by
    intro l
    induction l with
    | nil =>
      intro _ x hx a b
      simp only [List.map_nil, List.prod_nil, Module.End.one_apply]
      cases ha : ε a <;> cases hb : ε b
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
      · rw [hL b a hb ha x hx]; exact S.zero_mem
      · have h1 := gen [(a, b)] (by simp [ha, hb]) x hx
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h1
      · have h1 := gen [] (by simp) _ (hK a b (ha.trans hb.symm) x hx)
        simpa only [List.map_nil, List.prod_nil, Module.End.one_apply] using h1
    | cons q l ih =>
      obtain ⟨c, d⟩ := q
      intro hl x hx a b
      have hl' : ∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false := fun p hp => hl p (List.mem_cons_of_mem _ hp)
      have hcd : ε c = true ∧ ε d = false := hl (c, d) (by simp)
      have ih' := ih hl' x hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      set z := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x
      have key : E a b (E c d z) = E c d (E a b z) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) z := by
        rw [← hG a b c d, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [key, LinearMap.sub_apply]
      refine S.add_mem (pre c d hcd.1 hcd.2 _ (ih' a b)) (S.sub_mem ?_ ?_)
      · split_ifs
        · exact ih' a d
        · rw [LinearMap.zero_apply]; exact S.zero_mem
      · split_ifs
        · exact ih' c b
        · rw [LinearMap.zero_apply]; exact S.zero_mem
  intro a b y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, x, hx, rfl⟩ := hz
    exact main l hl x hx a b
  | zero => rw [map_zero]; exact S.zero_mem
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact S.add_mem hu hv
  | smul r u _ hu => rw [map_smul]; exact S.smul_mem r hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSubstitutionThetaHeisenbergUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem setLIntegral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (e : G ≃+ G) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ Γ ↔ x ∈ Γ) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) (hfin : μ F ≠ ⊤) (φ : G → ENNReal)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in F, φ (e w) ∂μ = ∫⁻ w in F, φ w ∂μ := by
  let m : G ≃ᵐ G :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain Γ (e ⁻¹' F) (μ.map e.symm) := by
    let f : Γ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e.symm = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  have hac : μ.map e.symm ≪ μ := hc ▸ Measure.smul_absolutelyContinuous
  have hF'' : IsAddFundamentalDomain Γ F (μ.map e.symm) := hF.mono hac
  have h1 : (μ.map e.symm) (e ⁻¹' F) = μ F := hmp.measure_preimage_equiv F
  have h2 : (μ.map e.symm) F = μ F := (hF''.measure_eq hF').trans h1
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hc1 : (c : ENNReal) = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [h2, one_mul])
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc2, one_smul] at hc
  have h3 : ∫⁻ w in e ⁻¹' F, φ (e w) ∂(μ.map e.symm) = ∫⁻ w in F, φ w ∂μ :=
    hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding φ F
  rw [hc] at h3 hF'
  rw [← h3]
  refine hF.setLIntegral_eq hF' (fun w => φ (e w)) fun g x => ?_
  show φ (e ((g : G) + x)) = φ (e x)
  rw [map_add (f := _), hφ _ ((hΓ _).2 g.2)]

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem symplOH_actO (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.SymplOInv.symplO_actO]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem exists_actO_ratW {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ∃ y, actO S T γ γ' (ratW T S x) = ratW T S y := by
  obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actO ratW
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actO_mem_ratL {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) {x : WO S T}
    (hx : x ∈ ratL T S) : actO S T γ γ' x ∈ ratL T S := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actO_ratW hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem isThetaFunO_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) :
    IsThetaFunO ψ S T fun w => f (actO S T γ γ' w) := by
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := GlobalTheory.LatLevel.continuous_actO S T γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actO_ratW hγ hγ' x
    rw [actO_add, ← symplOH_actO γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.LatLevel.actO_map_inf S T γ γ' h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← symplOH_actO γ γ' w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have h3 : ∀ t, (actO S T γ γ' (L t)).map (finPart D) = 0 := fun t => by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem rational_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  intro D ψ hψ S T γ hγ γ' hγ' f hf
  have hi := (GQ S).inv_mem hγ
  have hi' := (GQ T).inv_mem hγ'
  refine ⟨isThetaFunO_comp hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext w
    unfold heisO
    beta_reduce
    rw [actO_add, actO_inv_actO, ← symplOH_actO γ⁻¹ γ'⁻¹ w, actO_inv_actO]
  · obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : Countable (ratL T S) := countable_of_discrete_addSubgroup _
    have hinv : ∀ x, actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ x) = x := fun x => by
      have := actO_inv_actO γ⁻¹ γ'⁻¹ x
      rwa [inv_inv, inv_inv] at this
    let e : WO S T ≃+ WO S T :=
      { toFun := actO S T γ⁻¹ γ'⁻¹
        invFun := actO S T γ γ'
        left_inv := hinv
        right_inv := actO_inv_actO γ γ'
        map_add' := actO_add _ _ }
    refine setLIntegral_comp_addEquiv (G := WO S T) (ratL T S) e (GlobalTheory.LatLevel.continuous_actO S T _ _)
      (GlobalTheory.LatLevel.continuous_actO S T _ _) (fun x => ⟨fun hx => ?_, actO_mem_ratL hi hi'⟩) μ h𝓕
      (measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hcov μ h𝓕).ne
      (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact actO_mem_ratL hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h6 : f (ratW T S y + x) = _ := hf.quasi y x
      have h7 : ‖f (ratW T S y + x)‖ = ‖f x‖ := by
        rw [h6, norm_mul, hψ.1.2.1, one_mul]
      show ‖f (ratW T S y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

end GlobalTheory.RatSubst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentableOfZariskiSheafOpenChartsLarge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_represent_of_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F hsep hglue Ix U x hinj hopen hcov
  haveI hs : FunctorToTypes.Small.{0} F := _root_.GlobalTheory.PicGlue.small_of_separated_of_open_charts F hsep Ix U x hopen hcov
  let G : Scheme.{0}ᵒᵖ ⥤ Type := FunctorToTypes.shrink.{0} F
  let e : ∀ T : Scheme.{0}, F.obj (op T) ≃ G.obj (op T) := fun T => equivShrink.{0} (F.obj (op T))
  have he : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : G.obj (op T)),
      G.map a.op y = e Y (F.map a.op ((e T).symm y)) := fun a y => rfl
  have he' : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : F.obj (op T)),
      G.map a.op (e T y) = e Y (F.map a.op y) := fun a y => by
    rw [he, Equiv.symm_apply_apply]
  have key := _root_.GlobalTheory.exists_universal_of_charts G ?_ ?_ Ix U (fun i => e _ (x i)) ?_ ?_ ?_
  · obtain ⟨B, x₀, hx⟩ := key
    obtain ⟨x₁, rfl⟩ := (e B).surjective x₀
    have hx' : ∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₁ = y := by
      intro T y
      have h := hx T (e T y)
      simpa only [he', Equiv.apply_eq_iff_eq] using h
    exact ⟨B, x₁, hx', _root_.GlobalTheory.charts_represented_open_cover F Ix U x hinj hopen hcov B x₁ hx'⟩
  · intro T y y' h
    obtain ⟨y, rfl⟩ := (e T).surjective y
    obtain ⟨y', rfl⟩ := (e T).surjective y'
    simp only [he', Equiv.apply_eq_iff_eq] at h
    rw [hsep T y y' h]
  · intro T J Z z y hz hc h
    obtain ⟨y₀, hy₀⟩ := hglue T J Z z (fun i => (e _).symm (y i)) hz hc (fun i k Y a b hab => by
      have h1 := h i k Y a b hab
      rw [he, he] at h1
      exact (e Y).injective h1)
    refine ⟨e T y₀, fun i => ?_⟩
    rw [he', hy₀, Equiv.apply_symm_apply]
  · intro i Y u u' h
    rw [he', he'] at h
    exact hinj i Y u u' ((e Y).injective h)
  · intro i T y
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hopen i T y
  · intro T y p
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hcov T y p

end GlobalTheory.PicGlue
end

