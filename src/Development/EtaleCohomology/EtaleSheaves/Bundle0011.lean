module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.Gluing₂

theorem orth {S : Type} [CommRing S] : ∀ (n : ℕ) (ε : Fin n → S), (∀ j, IsIdempotentElem (ε j)) →
    ∃ ε' : Fin n → S, OrthogonalIdempotents ε' ∧ (∀ j, ∃ c, ε' j = ε j * c) ∧
      ∑ j, ε' j = 1 - ∏ j, (1 - ε j) := by
  intro n
  induction n with
  | zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨ε₀, ho, hd, hs⟩ := ih (fun j => ε j.succ) (fun j => hε j.succ)
    have ha : IsIdempotentElem (ε 0) := hε 0
    have ha' : IsIdempotentElem (1 - ε 0) := ha.one_sub
    refine ⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simp only [Fin.cons_succ]
        exact ha'.mul (ho.idem j)
    · intro i k hik
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact absurd rfl hik
        | succ k =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
      | succ i =>
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
        | succ k =>
          simp only [Fin.cons_succ]
          have hik' : i ≠ k := fun h => hik (by rw [h])
          calc (1 - ε 0) * ε₀ i * ((1 - ε 0) * ε₀ k) = ((1 - ε 0) * (1 - ε 0)) * (ε₀ i * ε₀ k) := by ring
            _ = 0 := by rw [ho.ortho hik', mul_zero]
    · intro i
      refine Fin.cases ⟨1, by simp⟩ (fun j => ?_) i
      obtain ⟨c, hc⟩ := hd j
      exact ⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hs]
      ring

theorem glue : LateralTheory.E.FinEtSectionPf.Glue := by
  intro S C _ _ _ n e he hsurj ε hε hr hh
  obtain ⟨ε', ho, hd, hs⟩ := orth n ε hε

  have hf0 : ∏ j, (1 - ε j) = 0 := by
    have hidem : IsIdempotentElem (∏ j, (1 - ε j)) := by
      have := ho.isIdempotentElem_sum (s := Finset.univ).one_sub
      rwa [hs, sub_sub_cancel] at this
    refine hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)
    obtain ⟨q, hq⟩ := hsurj ⟨J, hJ⟩
    have : ∃ j, e j ∉ q.asIdeal := by
      by_contra hall
      push_neg at hall
      exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))
    obtain ⟨j, hj⟩ := this
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]; exact hj
    obtain ⟨q', rfl⟩ := hq'
    have hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S)) := by
      rw [← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩
    have hεj : ε j ∉ J := hmem
    have h1 : 1 - ε j ∈ J := by
      have : ε j * (1 - ε j) ∈ J := by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem
      exact (hJ.mem_or_mem this).resolve_left hεj
    exact J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1
  have hco : CompleteOrthogonalIdempotents ε' := ⟨ho, by rw [hs, hf0, sub_zero]⟩
  choose h hh using hh
  choose c hc using hd
  have hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j)) := by
    intro j
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩
    rw [← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]
    have hm := (Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))
    rwa [neg_sub] at hm
  let L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j} :=
    fun j => IsLocalization.Away.lift (ε j) (hunit j)
  let Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j}) :=
    RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))
  let E := RingEquiv.ofBijective _ hco.bijective_pi
  have hΦ : ∀ s : S, Φ (algebraMap S C s) = E s := by
    intro s
    funext j
    have := congrArg (fun g => L j (g s)) (hh j)
    simp only [RingHom.comp_apply] at this
    show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s
    rw [this]
    exact IsLocalization.Away.lift_eq (ε j) (hunit j) s
  refine ⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]
  simp

theorem Glue_of (_hL : LateralTheory.E.t_E1Cut.EtLift) (_hA : LateralTheory.E.t_E1Cut.EtAIC) : LateralTheory.E.FinEtSectionPf.Glue := glue

end LateralTheory.E.Gluing₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GoalOf
section
namespace LateralTheory.E.LeafA6ringCut

theorem goal_of (h5 : LateralTheory.E.CupProductRingLaws.LeafRingUnit) (h6 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc)
    (h7 : LateralTheory.E.CupProductRingLaws.LeafRingComm) : LateralTheory.E.D2.LeafA6ring :=
  fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩

end LateralTheory.E.LeafA6ringCut
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HZeroPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensIntPf
section
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

theorem local_of_finite (A S : Type) [CommRing A] [HenselianLocalRing A] [CommRing S] [Algebra A S]
    [Module.Finite A S] [Nontrivial S] (hid : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q
  rcases hid e he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · exact (H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))

theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem isLocal (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  haveI := sub_local A B hid {x}
  let y : Algebra.adjoin A ((({x} : Finset B)) : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin A _).val)
  · exact Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)

theorem maxIdeal_comap (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) :
    letI := isLocal A B hid
    letI := sub_local A B hid s
    (maximalIdeal B).comap (Algebra.adjoin A (s : Set B)).val = maximalIdeal (Algebra.adjoin A (s : Set B)) := by
  letI := isLocal A B hid
  letI := sub_local A B hid s
  haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A
  have : ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (fun x => Algebra.IsIntegral.isIntegral x) (maximalIdeal B)
  exact IsLocalRing.eq_maximalIdeal this

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : HenselianLocalRing B := by
  classical
  letI := isLocal A B hid
  refine ⟨fun f hf a0 h0 h1 => ?_⟩
  set s : Finset B := insert a0 f.coeffs
  let S := Algebra.adjoin A (s : Set B)
  letI := sub_local A B hid s
  haveI := sub_finite A B s
  haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc =>
    Algebra.subset_adjoin (by simp [s, hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, Algebra.subset_adjoin (by simp [s])⟩
  have hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B := fun y => by
    rw [← maxIdeal_comap A B hid s]; rfl
  have he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := fun p y => by
    rw [eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]; rfl
  have he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0 := fun p => he' p b0
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b0
    ((hmem _).2 (by rw [he, hgf]; exact h0))
    (by
      rw [← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]
      exact IsLocalRing.notMem_maximalIdeal.2 h1)
  refine ⟨a, ?_, (hmem _).1 ha'⟩
  rw [IsRoot.def, ← hgf, ← he', ha.eq_zero]; rfl

theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IECompPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.IECompPf
open LateralTheory.E.t_E3Cut

def UnderFA : Prop := ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X)

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

theorem et_comp : Et.IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (f ≫ g).hom.Etale
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ hf hg

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem et_fp : Et ≤ MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := fun _ _ f hf =>
  CommRingCat.isFinitelyPresentable_hom f (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf).2.2

theorem IEComp_of (h1 : UnderFA) (h2 : EtSpreads) : IEComp := by
  intro A B C f g hf hg
  have : ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X) := h1
  have : MorphismProperty.PreIndSpreads.{0} Et := h2
  have := et_comp
  have := et_cobase
  have := MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads (P := Et) et_fp
  exact this.comp_mem f g hf hg

end LateralTheory.E.IECompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntClosPf
section
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IntClosPf

theorem intMul {A C : Type} [CommRing A] [CommRing C] [IsDomain C] [Algebra A C] (z : C) (p : Polynomial A)
    (hp : ∃ n, algebraMap A C (p.coeff n) ≠ 0) (hz : Polynomial.aeval z p = 0) :
    ∃ a : A, algebraMap A C a ≠ 0 ∧ IsIntegral A (algebraMap A C a * z) := by
  let A' := (algebraMap A C).range
  letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap A A') := (algebraMap A C).rangeRestrict_surjective
  have : Algebra.IsIntegral A A' := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hsurj x
    exact isIntegral_algebraMap⟩
  set p' := p.map (algebraMap A A') with hp'def
  have h1 : Polynomial.aeval z p' = 0 := by rw [Polynomial.aeval_map_algebraMap]; exact hz
  have hp' : p' ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hp
    apply hn
    have : p'.coeff n = 0 := by rw [h0]; rfl
    rw [hp'def, Polynomial.coeff_map] at this
    have := congrArg Subtype.val this
    exact this
  have hint := isIntegral_leadingCoeff_smul p' z h1
  obtain ⟨a, ha⟩ := hsurj p'.leadingCoeff
  have hlc : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hval : algebraMap A C a = (p'.leadingCoeff : C) := by rw [← ha]; rfl
  refine ⟨a, ?_, ?_⟩
  · rw [hval]; intro h; exact hlc (Subtype.ext h)
  · have h2 : algebraMap A C a * z = p'.leadingCoeff • z := by rw [Algebra.smul_def, hval]; rfl
    rw [h2]
    exact isIntegral_trans _ hint

theorem IntClos_of (hH : HensInt) : IntClos := by
  intro A C c _ hSH hAIC hAR
  obtain ⟨hHA, -⟩ := hSH
  letI : Algebra A C := c.hom.toAlgebra
  let B := integralClosure A C
  refine ⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; rfl
  · intro x; exact integralClosure.isIntegral x
  · exact Subtype.val_injective
  · have hne : Nontrivial B := inferInstance
    obtain ⟨h⟩ := hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
    exact h.toIsLocalRing
  · intro p hm hdeg
    have hm' : (p.map B.val.toRingHom).Monic := hm.map _
    have hdeg' : 0 < (p.map B.val.toRingHom).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]; exact hdeg
    obtain ⟨r, hr⟩ := hAIC _ hm' hdeg'
    have hrB : IsIntegral B r := ⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩
    have hrA : IsIntegral A r := isIntegral_trans _ hrB
    have hrM : r ∈ B := hrA
    refine ⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩
    show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  · intro z
    have hQ : (⊥ : Ideal C).IsPrime := Ideal.isPrime_bot
    obtain ⟨p, ⟨n, hn⟩, hz⟩ := hAR ⊥ hQ z
    obtain ⟨a, ha, hint⟩ := intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩
      (by rw [Ideal.mem_bot] at hz; exact hz)
    refine ⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩

end LateralTheory.E.IntClosPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntPBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCBijPf

def TwGenNZAC : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (K : Type) [Field K] [IsAlgClosed K] (ζ : Prim q K) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

abbrev TwGenNZ : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

def LCSurj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Surjective (m B ζ)

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold Sec.res twGen ofRings.sec tw ofRings
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem gam_map {q : ℕ} {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) :
    gam (ζ.map f) = (gam ζ).map (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1) =
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1)
  have := congrArg (fun φ => φ.hom ζ.1) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem twGenNZ_of (hAC : TwGenNZAC) : TwGenNZ := by
  intro q _ i B _ _ ζ c h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ M) := Ideal.Quotient.field M
  let f : B →+* AlgebraicClosure (B ⧸ M) := (algebraMap (B ⧸ M) (AlgebraicClosure (B ⧸ M))).comp (Ideal.Quotient.mk M)
  apply hAC q i (AlgebraicClosure (B ⧸ M)) (ζ.map f) c
  have h2 := congrArg (Sec.res (Spec.map (CommRingCat.ofHom f))) h
  have hs : ∀ x : Sec (tw q i) (Spec (CommRingCat.of B)), Sec.res (Spec.map (CommRingCat.ofHom f)) (c.val • x) =
      c.val • Sec.res (Spec.map (CommRingCat.ofHom f)) x := fun x => map_nsmul _ _ x
  have hz : Sec.res (Spec.map (CommRingCat.ofHom f)) (0 : Sec (tw q i) (Spec (CommRingCat.of B))) = 0 := map_zero _
  rw [hs, hz, twGen_res, ← gam_map] at h2
  exact h2

theorem lcInj (hT : TwGenNZ) (q : ℕ) [NeZero q] (i : ℤ) m (hm : IsLCMap q i m) (B : Type) [CommRing B]
    (ζ : Prim q B) : Function.Injective (m B ζ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ hφ
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, φ p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LocallyConstant.ext h)
  set c := φ p with hc
  let U : Set (PrimeSpectrum B) := φ ⁻¹' {c}
  have hU : IsClosed U := (φ.isLocallyConstant.isClopen_fiber c).isClosed
  let I := PrimeSpectrum.vanishingIdeal U
  let f := Ideal.Quotient.mk I
  have hrange : Set.range (PrimeSpectrum.comap f) = U := by
    rw [_root_.range_comap_of_surjective _ f Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.closure_eq]
  have hconst : lcMap f φ = LocallyConstant.const _ c := by
    ext x
    have : PrimeSpectrum.comap f x ∈ U := hrange ▸ ⟨x, rfl⟩
    exact this
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    have hpU : p ∈ U := rfl
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).1 h1 p hpU))
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have h1 := hm.1 B (B ⧸ I) f ζ φ
  rw [hφ, hconst, hm.2] at h1
  simp only [map_zero] at h1
  exact hp (hT q i (B ⧸ I) (ζ.map f) c h1.symm)

theorem LCBij_of (hT : TwGenNZAC) (hS : LCSurj) : LateralTheory.E.LocallyConstantH0.LCBij :=
  fun q _ i m hm B _ ζ => ⟨lcInj (twGenNZ_of hT) q i m hm B ζ, hS q i m hm B ζ⟩

end LateralTheory.E.LCBijPf
end
end

