module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFilt

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechHdegOfSub
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem Cdeg_top (i : ℕ) : Cdeg G (fun I => (⊤ : Submodule R (G I))) i = ⊤ := by
  ext s
  simp [Cdeg]

theorem cocyDeg_top (i : ℕ) :
    cocyDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = LinearMap.ker (d G ρ i) := by
  rw [cocyDeg, Cdeg_top, inf_top_eq]

theorem bdryDeg_top (i : ℕ) :
    bdryDeg G (fun I => (⊤ : Submodule R (G I))) ρ i = bdry G ρ i := by
  cases i with
  | zero => rfl
  | succ i =>
    change (Cdeg G _ i).map (d G ρ i) = LinearMap.range (d G ρ i)
    rw [Cdeg_top, Submodule.map_top]

def hEquivHdegTop (i : ℕ) : H G ρ i ≃ₗ[R] Hdeg G (fun I => (⊤ : Submodule R (G I))) ρ i :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (cocyDeg_top G ρ i).symm) (by
    ext z
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    change (z : Cochain G i) ∈ bdry G ρ i ↔ (z : Cochain G i) ∈ bdryDeg G _ ρ i
    rw [bdryDeg_top])

end Cech

theorem CechHdegOfSub.proof : CechHdegOfSub.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ T n
  let φ : ∀ I : Chart x, T.sub I →ₗ[S] E := fun I =>
    { toFun := fun y => (y : E)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (m : T.sub I),
      φ J (T.res I J h m) = Cech.idRes S E (support x) I J h (φ I m) := fun _ _ _ _ => rfl
  have hdeg : ∀ (I : Chart x) (m : T.sub I), m ∈ (⊤ : Submodule S (T.sub I)) →
      φ I m ∈ (T.sub I).restrictScalars S := fun _ m _ => m.2
  have hinj : ∀ I, Function.Injective (φ I) := fun _ => Subtype.val_injective
  have hmap : ∀ I, (⊤ : Submodule S (T.sub I)).map (φ I) = (T.sub I).restrictScalars S := by
    intro I
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro h
      exact ⟨⟨y, h⟩, trivial, rfl⟩
  exact ⟨(Cech.hEquivHdegTop (fun I => T.sub I) T.res n).trans
    (LinearEquiv.ofBijective (Cech.mapHdeg _ _ φ hφ hdeg n)
      (Cech.Transport.proof.{u, v, v} (N + 1) (support x) S (fun I => T.sub I) (fun _ => E) T.res
        (Cech.idRes S E (support x)) _ _ φ hφ hdeg hinj hmap n))⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechPartition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem CechPartition.proof : CechPartition.Statement.{u, v, w} := by
  intro S _ Ω _ E _ _ _ n U M m a b j hjU hab ha hb hloc p s hs hds

  let T : Subring Ω :=
    { carrier := {c | ∀ I, ∀ z ∈ M I, c • z ∈ M I}
      mul_mem' := fun {x y} hx hy I z hz => by rw [mul_smul]; exact hx I _ (hy I z hz)
      one_mem' := fun I z hz => by rwa [one_smul]
      add_mem' := fun {x y} hx hy I z hz => by rw [add_smul]; exact (M I).add_mem (hx I z hz) (hy I z hz)
      zero_mem' := fun I z _ => by rw [zero_smul]; exact (M I).zero_mem
      neg_mem' := fun {x} hx I z hz => by rw [neg_smul]; exact (M I).neg_mem (hx I z hz) }
  have hT : ∀ c ∈ T, ∀ I, ∀ z ∈ M I, c • z ∈ M I := fun c hc => hc
  let b' : Fin m → T := fun k => ⟨b k, hb k⟩

  have hspan : Ideal.span (Set.range b') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (∑ k, (⟨a k, ha k⟩ : T) * b' k) = 1 := Subtype.ext (by simp [b', hab])
    rw [← h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

  have hex : ∀ (k : Fin m) (K : Cech.Idx U p), ∃ e0 : ℕ, j k ∉ K.1.1 →
      b k ^ e0 • Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M K.1 := by
    intro k K
    by_cases hk : j k ∈ K.1.1
    · exact ⟨0, fun h => absurd hk h⟩
    · let I' : Cell U := ⟨insert (j k) K.1.1, Finset.insert_nonempty _ _, Finset.insert_subset (hjU k) K.1.2.2⟩
      have hI' : I'.1.card = p + 1 + 1 := by
        change (insert (j k) K.1.1).card = p + 1 + 1
        rw [Finset.card_insert_of_notMem hk, K.2]
      have hz : Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M I' := by
        rw [show insert (j k) K.1.1 = (⟨I', hI'⟩ : Cech.Idx U (p + 1)).1.1 from rfl, Cech.Partition.onSet_idx]
        exact (Submodule.mem_pi.mp hs) ⟨I', hI'⟩ (Set.mem_univ _)
      obtain ⟨e0, he0⟩ := hloc k K.1 I' rfl _ hz
      exact ⟨e0, fun _ => he0⟩
  choose f hf using hex
  obtain ⟨e, he⟩ : ∃ e, ∀ k K, f k K ≤ e := by
    obtain ⟨e, he⟩ := (Set.finite_range (fun x : Fin m × Cech.Idx U p => f x.1 x.2)).bddAbove
    exact ⟨e, fun k K => he ⟨(k, K), rfl⟩⟩

  have hpow := Ideal.span_pow_eq_top (Set.range b') hspan e
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨c, hc⟩ := hpow

  let wt : Fin n → Ω := fun i => ∑ k ∈ Finset.univ.filter (fun k => j k = i), (c k : Ω) * b k ^ e
  have hw : ∑ i ∈ U, wt i = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun k _ => hjU k)]
    have h := congrArg Subtype.val hc
    simpa [b'] using h
  refine Cech.Partition.exact_of_partition M s hds wt hw ?_
  intro K i _ hiK
  simp only [wt, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain rfl := (Finset.mem_filter.mp hk).2
  rw [mul_smul, ← Nat.sub_add_cancel (he k K), pow_add, mul_smul]
  exact hT _ (c k).2 _ _ (hT _ (pow_mem (show b k ∈ T from hb k) _) _ _ (hf k K hiK))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u w

theorem CutComponent.proof (hZ : CutZeroNotLe.Statement.{u, w}) (hE : CutNonempty.Statement.{u, w})
    (hD : CutDimLower.Statement.{u, w}) : CutComponent.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hI
  obtain ⟨qq, hq, j, hj⟩ := hE k Ω N x n pp L s hW hL hs hI
  obtain ⟨f, hfZ, hfp⟩ := hZ k Ω N x (n + 1) pp L s hW hs hI
  have hlo := hD k Ω N x n pp L s qq hW hs hq ⟨j, hj⟩
  have hJq : pp ⊔ zeroIdeal L.toSubSystem s ≤ qq := hq.1.2
  have hqp : qq.IsPrime := hq.1.1
  have hppq : pp ≤ qq := le_sup_left.trans hJq
  have := hW.isPrime

  have hpH : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    intro i r hr
    have := hW.homog r hr i
    rwa [← decomposition.decompose'_apply] at this
  have hZH : (zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro f ⟨c, hc, -⟩; exact ⟨c, hc⟩)
  have hJH : (pp ⊔ zeroIdeal L.toSubSystem s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) := by
    have h := (HomogeneousIdeal.toIdeal_sup ⟨pp, hpH⟩ ⟨_, hZH⟩).symm ▸
      (⟨pp, hpH⟩ ⊔ ⟨_, hZH⟩ : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous
    exact h

  have hcore : qq ≤ (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
    refine hq.2 ⟨hqp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    rw [← hJH.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJq
  have hhom : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq := by
    intro p hp d
    have := (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).isHomogeneous d (hcore hp)
    have h2 : homogeneousComponent d p ∈
        (qq.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) k)).toIdeal := by
      rw [← decomposition.decompose'_apply]
      exact this
    exact Ideal.toIdeal_homogeneousCore_le _ _ h2

  have hup : ringKrullDim (Poly k N ⧸ qq) + 1 ≤ ((n + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hW.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hppq)
      (Ideal.Quotient.factor_surjective hppq) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hJq (Ideal.mem_sup_right hfZ)
  refine ⟨qq, hq, hqp, hhom, hW.le.trans hppq, ⟨j, hj⟩, ?_⟩

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize ringKrullDim (Poly k N ⧸ qq) = D at hup hlo ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hlo (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe m =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have h1 : n + 1 ≤ m := by exact_mod_cast hlo
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ ((n + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have h3 := Nat.cast_le.mp h2
      have : m = n + 1 := by omega
      subst this
      rfl

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section CutZeroNotLeAux

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_zeroIdeal_div_eq (D : SubFamily S x Ω) (hfg : ∀ K, (D.sub K).FG) (I : Chart x)
    {σ y : Ω} (hσ : σ ∈ D.sub I) (hy : ∀ δ ∈ D.sub I, y * δ ∈ chartRing S x I) :
    ∃ (g t : Poly S N) (n : ℕ), g ∈ zeroIdeal D.toSubSystem σ ∧ t ∈ monos I.1 ∧
      g.IsHomogeneous n ∧ t.IsHomogeneous n ∧ σ * y = aeval x g / aeval x t := by
  classical

  obtain ⟨f, s, n, hs, hf, hsn, hz⟩ := hy σ hσ
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hfz : y * σ * aeval x s = aeval x f := (eq_div_iff hs0).mp hz

  have hyU := mul_mem_chartRing_union D I
  choose G hG using hfg
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (D.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)

  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  have hUK : ∀ (K : Chart x), ∀ δ ∈ D.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
    intro K δ hδ
    rw [← hG K] at hδ
    induction hδ using Submodule.span_induction with
    | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
        ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hb
  have hU0 := eval_ne_zero_of_mem_monos I hUm

  have hfU : f * U ∈ zeroIdeal D.toSubSystem σ := by
    refine Ideal.subset_span ⟨n + dU, hf.mul hUh, fun K δ hδ => ?_⟩
    refine ⟨aeval x s * (aeval x U * (y * δ)), ?_, ?_⟩
    · rw [Nat.cast_add]
      exact twistMod_mul_mem (aeval_mem_twistMod hsn K) (hUK K δ hδ)
    · rw [map_mul, ← hfz]
      ring
  refine ⟨f * U, s * U, n + dU, hfU, mul_mem hs hUm, hf.mul hUh, hsn.mul hUh, ?_⟩
  rw [map_mul, map_mul, ← hfz]
  field_simp

end CutZeroNotLeAux

theorem CutZeroNotLe.proof : CutZeroNotLe.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp L s _ hs ⟨I, hI⟩
  have hsI : s ∈ L.sub I := (Submodule.mem_iInf _).mp hs I
  obtain ⟨P, hP⟩ := L.invertible I

  have hex : ∃ y ∈ P, s * y ∉ idealMod pp I := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [SubSystem.twist_sub_eq_mul_sub]
    have hle : Submodule.span (chartRing k x I) {s} * P ≤ idealMod pp I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (hcon b hb)
    have hmem : s ∈ Submodule.span (chartRing k x I) {s} * P * L.sub I := by
      rw [mul_assoc, mul_comm P, hP, mul_one]
      exact Submodule.mem_span_singleton_self s
    exact mul_le_mul' hle le_rfl hmem
  obtain ⟨y, hyP, hsy⟩ := hex
  have hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing k x I := by
    intro δ hδ
    have h := Submodule.mul_mem_mul hδ hyP
    rw [hP] at h
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp h
    rw [mul_comm, ← ha]
    exact a.2
  obtain ⟨g, t, n, hg, ht, hgn, htn, hst⟩ := exists_zeroIdeal_div_eq L.toSubFamily L.fg I hsI hy
  refine ⟨g, hg, fun hgp => hsy ?_⟩
  rw [hst]
  exact Submodule.subset_span ⟨g, t, n, hgp, ht, hgn, htn, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFilt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Filt.telescope : ∀ {n : ℕ} (a : Fin (n + 1) → ℤ) (b : Fin n → ℤ),
    (∀ l : Fin n, a l.castSucc = a l.succ + b l) → a 0 = a (Fin.last n) + ∑ l, b l
  | 0, a, b, _ => by simp
  | n + 1, a, b, h => by
    have ih := CycleSplit.Filt.telescope (fun m => a m.castSucc) (fun l => b l.castSucc)
      (fun l => by
        have := h l.castSucc
        simpa only [Fin.succ_castSucc] using this)
    have hl := h (Fin.last n)
    rw [Fin.succ_last] at hl
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero] at ih
    linarith


open SectionCount.Drop.Filt in
theorem CycleSplit.Filt.proof (hS : CycleSplit.Filt.Step.Statement.{u, w}) :
    CycleSplit.Filt.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 J hJhom hJx hJ𝔪

  have hkill : ∀ p ∈ primeOf (S := S) x, ∀ m : Poly S N ⧸ J, p • m = 0 := by
    intro p hp m
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk J (p * m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right m (hJx hp))
  obtain ⟨⟨Fl⟩, hcount⟩ := PrimeFiltration.Exists.proof.{u, u, w} S Ω N x (Poly S N ⧸ J)
    (quotGraded J hJhom) (finite_quot J) hkill
  rw [Ideal.annihilator_quotient] at hcount
  have hann : ∀ l, J ≤ Fl.prime l := fun l => by
    have := Fl.ann_le l; rwa [Ideal.annihilator_quotient] at this

  have hlift : ∀ l : Fin Fl.n, ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      Ideal.Quotient.mk J g = Fl.gen l := by
    intro l
    obtain ⟨g, hg, hgm⟩ := mem_quotGraded_piece.mp (Fl.gen_mem l)
    by_cases h0 : 0 ≤ Fl.deg l
    · refine ⟨g, (Fl.deg l).toNat, isHomogeneous_of_isWeightedHomogeneous_one ?_, hgm⟩
      rwa [Int.toNat_of_nonneg h0]
    · refine ⟨0, 0, isHomogeneous_zero _ _ _, ?_⟩
      have hg0 : g = 0 := by
        ext m
        by_contra hne
        have h1 := hg hne
        rw [weight_one_int] at h1
        omega
      rw [← hgm, hg0]
  choose g eK hgH hgm using hlift

  let Jk : Fin (Fl.n + 1) → Ideal (Poly S N) := fun l => (Fl.step l).comap J.mkQ
  have hJ0 : Jk 0 = J := by
    simp only [Jk, Fl.step_zero, Submodule.comap_bot, Submodule.ker_mkQ]
  have hJlast : Jk (Fin.last _) = ⊤ := by
    simp only [Jk, Fl.step_last, Submodule.comap_top]
  have hmkQ : ∀ (c : Poly S N) (l : Fin Fl.n), J.mkQ (c * g l) = c • Fl.gen l := by
    intro c l
    rw [← hgm l]
    rfl
  have hJsucc : ∀ l : Fin Fl.n, Jk l.succ = Jk l.castSucc ⊔ Ideal.span {g l} := by
    intro l
    ext f
    simp only [Jk, Fl.step_succ, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have h1 : f - c * g l ∈ (Fl.step l.castSucc).comap J.mkQ := by
        rw [Submodule.mem_comap, map_sub, hmkQ, ← hay, add_sub_cancel_right]
        exact ha
      have h2 := Submodule.add_mem_sup h1 (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self (g l)))
      rwa [sub_add_cancel] at h2
    · intro hf
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [map_add (f := _), hmkQ]
      exact Submodule.add_mem_sup ha (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hJkp : ∀ (l : Fin Fl.n) (f : Poly S N), f ∈ Fl.prime l ↔ f * g l ∈ Jk l.castSucc := by
    intro l f
    rw [Fl.mem_prime, ← hgm l]
    exact Iff.rfl
  have hJk_ge : ∀ l, J ≤ Jk l := fun l f hf => by
    simp only [Jk, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero J).mpr hf, zero_mem]
  have hJk_hom : ∀ l, ∀ f ∈ Jk l, ∀ d : ℕ, homogeneousComponent d f ∈ Jk l := by
    intro l
    induction l using Fin.induction with
    | zero => rw [hJ0]; exact hJhom
    | succ l ih =>
      rw [hJsucc l]
      exact hom_sup ih (hom_span fun g' hg' => ⟨eK l, by rw [Set.mem_singleton_iff.mp hg']; exact hgH l⟩)
  refine ⟨Fl.n, Fl.prime, fun l => -((eK l : ℕ) : ℤ),
    fun l => ⟨Fl.isPrime l, Fl.isHomogeneous l, hann l⟩, fun G _ hG => hcount Fl G hG, fun Q => ?_⟩

  have hstep : ∀ l : Fin Fl.n, ∀ᶠ c : ℕ in atTop,
      restrLen (Jk l.castSucc) (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (Jk l.succ) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ)))) := by
    intro l
    rw [hJsucc l]
    exact hS S Ω N x 𝔪 h𝔪 (Jk l.castSucc) (Fl.prime l) (g l) (eK l) (hJk_hom _)
      (hJx.trans (hJk_ge _)) (hJ𝔪.trans (hJk_ge _)) (hgH l) (Fl.isHomogeneous l) (hJkp l) Q
  filter_upwards [Filter.eventually_all.mpr hstep] with c hc
  have htel := CycleSplit.Filt.telescope
    (fun m => restrLen (Jk m) (Q.twist (twistSys S x (c : ℤ))))
    (fun l => restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ))))) hc
  simp only [hJ0, hJlast, restrLen_of_irrelevant ⊤ (fun i => Submodule.mem_top), zero_add] at htel
  rw [htel]
  simp only [sub_eq_add_neg]

end GroundTheory.Heights₂.Heights.Kleiman
end

