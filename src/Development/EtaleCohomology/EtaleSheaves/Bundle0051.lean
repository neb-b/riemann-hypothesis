module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0042
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartAPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartAPf

variable {B : Type} [CommRing B]

theorem one_mem_S (I : Ideal B) {e : B ⧸ I} {u : B} (hu : Ideal.Quotient.mk I u = e) (he : IsIdempotentElem e) :
    u ∈ S I e := ⟨1, by rw [hu, mul_one, he.eq]⟩

theorem mem_map_of_comp (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P)
    (hz : ∀ e : P.1, z e ∈ I.map (algebraMap B (Localization (S I e.1)))) : z ∈ I.map (βP I P) := by
  classical
  choose a ha using fun e : P.1 =>
    (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 (hz e)
  have key : z = ∑ e : P.1, βP I P ((a e).1 : B) *
      Pi.single e (IsLocalization.mk' (Localization (S I e.1)) (1 : B) (a e).2) := by
    funext e'
    rw [Finset.sum_apply, Finset.sum_eq_single e']
    · simp only [Pi.mul_apply, Pi.single_eq_same, βP, RingHom.pi_apply]
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
      exact ha e'
    · intro e _ hne
      simp [Pi.single_eq_of_ne' hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a e).1.2)

theorem comp_mem (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P) (hz : z ∈ I.map (βP I P)) (e : P.1) :
    z e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h := Ideal.mem_map_of_mem (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) hz
  rw [Ideal.map_map] at h
  exact h

theorem sum_mul_single (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (c : P.1 → B ⧸ I) (e' : P.1) :
    (∑ e : P.1, c e * e.1) * e'.1 = c e' * e'.1 := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single e']
  · rw [mul_assoc, (P.idem e'.1 e'.2).1.eq]
  · intro e _ hne
    rw [mul_assoc, P.orth e.1 e.2 e'.1 e'.2 (fun h => hne (Subtype.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem PartA_of : PartA := by
  intro B _ I P
  classical
  constructor
  · apply Ideal.quotientMap_injective'
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcomp : ∀ e : P.1, Ideal.Quotient.mk I x * e.1 = 0 := by
      intro e
      have h := comp_mem I P _ hx e
      obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 h
      simp only [βP, RingHom.pi_apply] at hs
      rw [← map_mul] at hs
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (S I e.1) (Localization (S I e.1))).1 hs
      have hq := congrArg (Ideal.Quotient.mk I) hc
      rw [map_mul, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 i.2, mul_zero] at hq
      obtain ⟨t, ht⟩ := c.2
      obtain ⟨t', ht'⟩ := s.2
      calc Ideal.Quotient.mk I x * e.1
          = Ideal.Quotient.mk I x * ((Ideal.Quotient.mk I c * t * e.1) * (Ideal.Quotient.mk I s * t' * e.1)) := by
            rw [ht, ht', (P.idem e.1 e.2).1.eq]
        _ = (Ideal.Quotient.mk I c * (Ideal.Quotient.mk I x * Ideal.Quotient.mk I s)) * (t * t' * e.1 * e.1) := by ring
        _ = 0 := by rw [hq, zero_mul]
    calc Ideal.Quotient.mk I x = Ideal.Quotient.mk I x * ∑ e ∈ P.1, e := by rw [P.sum_eq, mul_one]
      _ = ∑ e : P.1, Ideal.Quotient.mk I x * e.1 := by
          rw [Finset.mul_sum, ← Finset.sum_coe_sort P.1]
      _ = 0 := Finset.sum_eq_zero fun e _ => hcomp e
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hB : ∀ e : P.1, ∃ (b : B) (s : S I e.1), IsLocalization.mk' (Localization (S I e.1)) b s = y e :=
      fun e => by
        obtain ⟨⟨b, s⟩, h⟩ := IsLocalization.mk'_surjective (S I e.1) (y e)
        exact ⟨b, s, h⟩
    choose b s hbs using hB
    have hS : ∀ e : P.1, ∃ t, Ideal.Quotient.mk I (s e : B) * t * e.1 = e.1 := fun e => (s e).2
    choose t ht using hS
    choose τ hτ using fun e : P.1 => Ideal.Quotient.mk_surjective (t e)
    choose ε hε using fun e : P.1 => Ideal.Quotient.mk_surjective e.1
    refine ⟨Ideal.Quotient.mk _ (∑ e : P.1, b e * τ e * ε e), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    apply mem_map_of_comp
    intro e'
    set x := ∑ e : P.1, b e * τ e * ε e
    have hεS : ε e' ∈ S I e'.1 := one_mem_S I (hε e') (P.idem e'.1 e'.2).1
    rw [IsLocalization.mem_map_algebraMap_iff (S I e'.1) (Localization (S I e'.1))]
    refine ⟨⟨⟨(x * s e' - b e') * ε e', ?_⟩, s e' * ⟨ε e', hεS⟩⟩, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_mul, hε]
      have hx : Ideal.Quotient.mk I x = ∑ e : P.1, (Ideal.Quotient.mk I (b e) * t e) * e.1 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [x, map_sum, map_mul, hτ, hε]
      rw [sub_mul, mul_right_comm, hx, sum_mul_single]
      calc Ideal.Quotient.mk I (b e') * t e' * e'.1 * Ideal.Quotient.mk I (s e') - Ideal.Quotient.mk I (b e') * e'.1
          = Ideal.Quotient.mk I (b e') * (Ideal.Quotient.mk I (s e') * t e' * e'.1) - Ideal.Quotient.mk I (b e') * e'.1 := by ring
        _ = 0 := by rw [ht e', sub_self]
    · simp only [Pi.sub_apply, βP, RingHom.pi_apply, Submonoid.coe_mul, map_mul, map_sub, ← hbs e']
      rw [sub_mul, sub_mul, ← mul_assoc (IsLocalization.mk' _ _ _), IsLocalization.mk'_spec]
      ring

end LateralTheory.E.PartAPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartCPf
section
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPf

def Split : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)), p.Monic →
    ∃ (n : ℕ) (r : Fin n → PiLocalization₂ I P), p = ∏ l, (X - C (r l))

def Idem : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (n : ℕ) (y : Fin n → PiLocalization₂ I P),
  ∏ l, y l ∈ I.map (βP I P) →
  IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, y m)) →
  ∃ f : Fin n → B, (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) ∧
    (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) ∧
    ∑ l, Ideal.Quotient.mk I (f l) = 1 ∧ ∀ l, βP I P (f l) * y l ∈ I.map (βP I P)

def Lift : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P)
  (n : ℕ) (r : Fin n → PiLocalization₂ I P) (f : Fin n → B), p = ∏ l, (X - C (r l)) →
  (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) →
  (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) →
  ∑ l, Ideal.Quotient.mk I (f l) = 1 → (∀ l, βP I P (f l) * (a₀ - r l) ∈ I.map (βP I P)) →
  ∃ (Q : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
    a - stageMap I h a₀ ∈ I.map (βP I Q)

theorem eval_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (∏ l, (X - C (r l))).eval x = ∏ l, (x - r l) := by
  simp [eval_prod]

theorem deriv_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (derivative (∏ l, (X - C (r l)))).eval x = ∑ l, ∏ m ∈ Finset.univ.erase l, (x - r m) := by
  classical
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

theorem PartC_of (hs : Split) (hi : Idem) (hl : Lift) : LateralTheory.E.PartDiagCut.PartC := by
  intro B _ _ I hB P p a₀ hm hev hder
  obtain ⟨n, r, hp⟩ := hs B I hB P p hm
  have h1 : ∏ l, (a₀ - r l) ∈ I.map (βP I P) := by
    rw [← eval_prod_lin n r a₀, ← hp]; exact hev
  have h2 : IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, (a₀ - r m))) := by
    rw [← deriv_prod_lin n r a₀, ← hp]; exact hder
  obtain ⟨f, hfi, hfo, hfs, hfy⟩ := hi B I P n (fun l => a₀ - r l) h1 h2
  exact hl B I P p a₀ n r f hp hfi hfo hfs hfy

theorem idem_of (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) : Idem := by
  intro B _ I P n y hprod hsum
  let φ := RingEquiv.ofBijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map) (hA B I P)
  obtain ⟨e, hei, heo, hes, hey⟩ := hIP (PiLocalization₂ I P ⧸ I.map (βP I P)) n
    (fun l => Ideal.Quotient.mk (I.map (βP I P)) (y l))
    (by rw [← map_prod]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod)
    (by simpa [map_sum, map_prod] using hsum)
  choose f hf using fun l => Ideal.Quotient.mk_surjective (φ.symm (e l))
  refine ⟨f, fun l => ?_, fun l m hlm => ?_, ?_, fun l => ?_⟩
  · unfold IsIdempotentElem; rw [hf, ← map_mul, (hei l).eq]
  · rw [hf, hf, ← map_mul, heo l m hlm, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp_rw [hf]; rw [← map_sum, hes, map_one]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    have h1 : φ (Ideal.Quotient.mk I (f l)) = e l := by rw [hf]; exact φ.apply_symm_apply _
    have h2 : Ideal.Quotient.mk (I.map (βP I P)) (βP I P (f l)) = e l := by
      rw [← h1]; simp [φ, Ideal.quotientMap_mk]
    rw [h2]; exact hey l

theorem PartC_of' (hs : Split) (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) (hl : Lift) :
    LateralTheory.E.PartDiagCut.PartC :=
  PartC_of hs (idem_of hIP hA) hl

end LateralTheory.E.PartCPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartDirectedPf
section
namespace LateralTheory.E.PartDirectedPf

variable {A : Type} [CommRing A]

theorem prod_eq_zero_of_ne {a b c d : A} (P Q : PartDiagCut.Part A)
    (ha : a ∈ P.blocks) (hb : b ∈ Q.blocks) (hc : c ∈ P.blocks) (hd : d ∈ Q.blocks)
    (hne : (a, b) ≠ (c, d)) : (a * b) * (c * d) = 0 := by
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; exact hne (by rw [hac, h])
    have := Q.orth b hb d hd hbd
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, mul_zero]
  · have := P.orth a ha c hc hac
    calc a * b * (c * d) = a * c * (b * d) := by ring
      _ = 0 := by rw [this, zero_mul]

open Classical in
noncomputable def meet (P Q : PartDiagCut.Part A) : PartDiagCut.Part A where
  blocks := ((P.blocks ×ˢ Q.blocks).filter (fun x => x.1 * x.2 ≠ 0)).image (fun x => x.1 * x.2)
  idem := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hne⟩, rfl⟩ := he
    exact ⟨(P.idem a ha).1.mul (Q.idem b hb).1, hne⟩
  orth := by
    intro e he e' he' hee
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he he'
    obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
    obtain ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, _⟩, rfl⟩ := he'
    refine prod_eq_zero_of_ne P Q ha hb hc hd ?_
    intro h; apply hee; simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
  sum_eq := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter_ne_zero, Finset.sum_product, ← Finset.sum_mul_sum,
        P.sum_eq, Q.sum_eq, mul_one]
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx hy
      by_contra hne
      have h0 := prod_eq_zero_of_ne P Q hx.1.1 hx.1.2 hy.1.1 hy.1.2 hne
      change x.1 * x.2 = y.1 * y.2 at hxy
      rw [← hxy] at h0
      have hid : IsIdempotentElem (x.1 * x.2) := (P.idem _ hx.1.1).1.mul (Q.idem _ hx.1.2).1
      exact hx.2 (by rw [← hid.eq]; exact h0)

theorem le_meet_left (P Q : PartDiagCut.Part A) : P ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨a, ha, ?_⟩
  calc a * b * a = a * a * b := by ring
    _ = a * b := by rw [(P.idem a ha).1.eq]

theorem le_meet_right (P Q : PartDiagCut.Part A) : Q ≤ meet P Q := by
  intro e he
  simp only [meet, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, rfl⟩ := he
  refine ⟨b, hb, ?_⟩
  calc a * b * b = a * (b * b) := by ring
    _ = a * b := by rw [(Q.idem b hb).1.eq]

theorem part_nonempty (A : Type) [CommRing A] : Nonempty (PartDiagCut.Part A) := by
  by_cases h : Nontrivial A
  · exact ⟨{ blocks := {1}
             idem := by intro e he; rw [Finset.mem_singleton] at he; subst he; exact ⟨IsIdempotentElem.one, one_ne_zero⟩
             orth := by intro e he e' he' hne; rw [Finset.mem_singleton] at he he'; exact absurd (he.trans he'.symm) hne
             sum_eq := by simp }⟩
  · rw [not_nontrivial_iff_subsingleton] at h
    exact ⟨{ blocks := ∅
             idem := by simp
             orth := by simp
             sum_eq := Subsingleton.elim _ _ }⟩

theorem PartDirected_of : LateralTheory.E.PartDiagCut.PartDirected := by
  intro A _
  exact ⟨⟨fun P Q => ⟨meet P Q, le_meet_left P Q, le_meet_right P Q⟩⟩, part_nonempty A⟩

end LateralTheory.E.PartDirectedPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProdPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.ProdPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} (g : X ⟶ S) (a : P' ⟶ P) (q' : P' ⟶ X), IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' g a q' h
    have : IsIso (pullback.snd e g) := inferInstance
    have hq' : q' = h.isoPullback.hom ≫ pullback.snd e g := (IsPullback.isoPullback_hom_snd h).symm
    rw [hq']
    exact IterLine.iso _ inferInstance
  | comp l k hl _ ih =>
    intro X P' g a q' h
    have w : q' ≫ g = (a ≫ l) ≫ k := by rw [Category.assoc, ← h.w]
    let m := pullback.lift q' (a ≫ l) w
    have hb : IsPullback (pullback.snd g k) (pullback.fst g k) k g := (IsPullback.of_hasPullback g k).flip
    have e1 : m ≫ pullback.fst g k = q' := pullback.lift_fst _ _ _
    have e2 : m ≫ pullback.snd g k = a ≫ l := pullback.lift_snd _ _ _
    have hs : IsPullback a (m ≫ pullback.fst g k) (l ≫ k) g := by
      rw [e1]; exact h
    have ht : IsPullback a m l (pullback.snd g k) := IsPullback.of_bot hs e2.symm hb
    have hm : IsLine m := hl.bc ht
    have e : q' = m ≫ pullback.fst g k := e1.symm
    rw [e]
    exact IterLine.comp _ _ hm (ih g (pullback.snd g k) (pullback.fst g k) hb)

theorem exists_widePullback_of_iteratedLine (hI : IterComp) {S : Scheme.{0}} : ∀ (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S),
    (∀ j, IterLine (qj j)) →
    ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
        ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j := by
  intro n
  induction n with
  | zero =>
    intro Pj qj _
    refine ⟨S, 𝟙 S, fun j => j.elim0, IterLine.iso _ inferInstance, fun j => j.elim0, ?_⟩
    intro T t f _
    refine ⟨t, ⟨by simp, fun j => j.elim0⟩, ?_⟩
    rintro g ⟨hg, -⟩
    simpa using hg
  | succ n ih =>
    intro Pj qj hqj
    obtain ⟨P0, q0, π0, hq0, hπ0, hU0⟩ := ih (fun j => Pj j.succ) (fun j => qj j.succ) (fun j => hqj j.succ)
    have hfst : IterLine (pullback.fst q0 (qj 0)) :=
      iterLine_of_isPullback (hqj 0) q0 (pullback.snd q0 (qj 0)) (pullback.fst q0 (qj 0))
        (IsPullback.of_hasPullback q0 (qj 0)).flip
    let π : ∀ j, pullback q0 (qj 0) ⟶ Pj j :=
      Fin.cases (motive := fun j => pullback q0 (qj 0) ⟶ Pj j) (pullback.snd q0 (qj 0))
        (fun j => pullback.fst q0 (qj 0) ≫ π0 j)
    have hπ0' : π 0 = pullback.snd q0 (qj 0) := rfl
    have hπs : ∀ j : Fin n, π j.succ = pullback.fst q0 (qj 0) ≫ π0 j := fun j => rfl
    refine ⟨pullback q0 (qj 0), pullback.fst q0 (qj 0) ≫ q0, π, hI _ _ hfst hq0, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hπ0', ← pullback.condition]
      · rw [hπs, Category.assoc, hπ0]
    · intro T t f hf
      obtain ⟨g0, ⟨hg0q, hg0π⟩, hu⟩ := hU0 t (fun j => f j.succ) (fun j => hf j.succ)
      have w : g0 ≫ q0 = f 0 ≫ qj 0 := by rw [hg0q, hf 0]
      refine ⟨pullback.lift g0 (f 0) w, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, pullback.lift_fst, hg0q]
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [hπ0', pullback.lift_snd]
        · rw [hπs, ← Category.assoc, pullback.lift_fst, hg0π]
      · rintro g' ⟨hg'q, hg'π⟩
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply hu
          refine ⟨by rw [Category.assoc, hg'q], fun j => ?_⟩
          rw [Category.assoc, ← hπs, hg'π]
        · rw [pullback.lift_snd, ← hπ0', hg'π]

theorem Prod_of (hI : IterComp) : LateralTheory.E.ChowGraphCut.Prod := by
  intro S n Pj qj hq
  exact exists_widePullback_of_iteratedLine hI n Pj qj hq

end LateralTheory.E.ProdPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelDescPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.RelDescPf

theorem hkpull_comp (R : Type) [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨y, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  change (Cochain.ofHom (a ≫ b)).comp y.1 (zero_add n) =
    (Cochain.ofHom a).comp ((Cochain.ofHom b).comp y.1 (zero_add n)) (zero_add n)
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) comm'' = rmap R f' f'' u' e' comm' ≫ rmap R f f' u e comm := by
  simp only [rmap, Functor.map_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

theorem rpull_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (comm : f' ≫ e = u ≫ f) (comm' : f'' ≫ e' = u' ≫ f')
    (comm'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    rpull R f f'' (u' ≫ u) (e' ≫ e) comm'' F n y = rpull R f' f'' u' e' comm' F n (rpull R f f' u e comm F n y) := by
  simp only [rpull]
  rw [rmap_comp R f f' f'' u e u' e' comm comm' comm'']
  exact hkpull_comp R _ _ F n y

def RelEqvInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f), Eqv R u F → Eqv R e F → ∀ n : ℤ, Function.Injective (rpull R f f' u e comm F n)

def CechEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E)
  (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''), Et e → SpS e → IsPushout φ' e u φ'' →
  Eqv (ZMod q) (cechAug (Spec.map e)) (tw q i) ∧ Eqv (ZMod q) (cechAug (Spec.map u)) (tw q i)

def LevelInj : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → IsPushout φ' e u φ'' →
  ∃ (g : cech (Spec.map u) ⟶ cech (Spec.map e)) (_hA : g ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ'))
    (i0 : sch.obj (Spec E) ⟶ cech (Spec.map e)) (j0 : sch.obj (Spec Y'') ⟶ cech (Spec.map u))
    (h0 : sch.map (Spec.map φ'') ≫ i0 = j0 ≫ g),
    i0 ≫ cechAug (Spec.map e) = sch.map (Spec.map e) ∧ j0 ≫ cechAug (Spec.map u) = sch.map (Spec.map u) ∧
    Function.Injective (rpull (ZMod q) g (sch.map (Spec.map φ'')) j0 i0 h0 (tw q i) n)

theorem relDesc_of (hEq : RelEqvInj) (hC : CechEqv) (hL : LevelInj) : LateralTheory.E.TruncationKernel.RelDesc := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨g, hA, i0, j0, h0, hi, hj, hinj⟩ := hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  obtain ⟨hCe, hCu⟩ := hC hH q i φ' e u φ'' he hs hpo'
  have h1 := hEq (ZMod q) (tw q i) (sch.map (Spec.map φ')) g (cechAug (Spec.map u)) (cechAug (Spec.map e)) hA hCu hCe n
  have key : ∀ (a : sch.obj (Spec Y'') ⟶ sch.obj (Spec Y')) (b : sch.obj (Spec E) ⟶ sch.obj (Spec D))
      (ha : j0 ≫ cechAug (Spec.map u) = a) (hb : i0 ≫ cechAug (Spec.map e) = b)
      (c : sch.map (Spec.map φ'') ≫ b = a ≫ sch.map (Spec.map φ')),
      Function.Injective (rpull (ZMod q) (sch.map (Spec.map φ')) (sch.map (Spec.map φ'')) a b c (tw q i) n) := by
    intro a b ha hb c
    subst ha hb
    intro x y hxy
    rw [rpull_comp _ _ g _ _ _ _ _ hA h0 c, rpull_comp _ _ g _ _ _ _ _ hA h0 c] at hxy
    exact h1 (hinj hxy)
  exact key _ _ hj hi _

theorem etale_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (he : Et e) : Etale (Spec.map e) :=
  HasRingHomProperty.Spec_iff.mpr he

theorem surj_spec {D E : CommRingCat.{0}} (e : D ⟶ E) (hs : SpS e) : Surjective (Spec.map e) := by
  constructor
  intro x
  obtain ⟨Q, hQ, hQr⟩ := hs x.asIdeal x.isPrime
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQr⟩

theorem cechEqv : CechEqv := by
  intro hH q _ i D Y' E Y'' φ' e u φ'' he hs hpo
  have hpb := isPullback_SpecMap_of_isPushout φ' e u φ'' hpo
  have hE : Etale (Spec.map e) := etale_spec e he
  have hS : Surjective (Spec.map e) := surj_spec e hs
  have hEu : Etale (Spec.map u) := MorphismProperty.of_isPullback (P := @Etale) hpb.flip hE
  have hSu : Surjective (Spec.map u) := MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hS
  exact ⟨hH.2.1 (ZMod q) (Spec.map e) (tw q i), hH.2.1 (ZMod q) (Spec.map u) (tw q i)⟩

end LateralTheory.E.RelDescPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelNormPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

theorem closedAt_comp {X N T : Scheme.{0}} (c' : X ⟶ N) (k' : N ⟶ T) (V : T.Opens)
    (h : ClosedAt c' (k' ⁻¹ᵁ V)) (hs : Function.Surjective (k'.app V)) : ClosedAt (c' ≫ k') V := by
  intro b hb
  obtain ⟨p, hm, hp⟩ := hb
  obtain ⟨a', ha'⟩ := h b ⟨p.map (k'.app V).hom, hm.map _, (Polynomial.eval₂_map (p := p) (k'.app V).hom (c'.app (k' ⁻¹ᵁ V)).hom b).trans hp⟩
  obtain ⟨a, rfl⟩ := hs a'
  exact ⟨a, ha'⟩

theorem normClosed : NormClosed := by
  intro Z S g _ _ _ V hV
  have H : g = g.toNormalization.toNormalization ≫
      (g.toNormalization.fromNormalization ≫ g.fromNormalization) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      Scheme.Hom.toNormalization_fromNormalization]
  let h := g.normalizationDesc _ _ H
  have e1 : g.toNormalization ≫ h = g.toNormalization.toNormalization :=
    g.toNormalization_normalizationDesc _ _ H
  have e2 : h ≫ g.toNormalization.fromNormalization ≫ g.fromNormalization = g.fromNormalization :=
    g.normalizationDesc_comp _ _ H
  have i1 : h ≫ g.toNormalization.fromNormalization = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
      (by rw [reassoc_of% e1, Scheme.Hom.toNormalization_fromNormalization, Category.comp_id])
      (by rw [Category.assoc, e2]) (Category.id_comp _)
  have i2 : g.toNormalization.fromNormalization ≫ h = 𝟙 _ :=
    Scheme.Hom.normalization.hom_ext g.toNormalization _ _ g.toNormalization.fromNormalization
      (by rw [Scheme.Hom.toNormalization_fromNormalization_assoc, e1, Category.comp_id])
      (by rw [Category.assoc, i1, Category.comp_id]) (Category.id_comp _)
  have : IsIso g.toNormalization.fromNormalization := ⟨h, i2, i1⟩
  have e := g.toNormalization.toNormalization_fromNormalization
  rw [← e]
  exact closedAt_comp _ _ V (closedAt_preimage _ V hV)
    (ConcreteCategory.bijective_of_isIso (g.toNormalization.fromNormalization.app V)).2

theorem RelNorm_of : LateralTheory.E.SteinPf.RelNorm := RelNorm_of_closed normClosed

end LateralTheory.E.RelNormPf
end
end

