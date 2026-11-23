module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHensSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem split_monic (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] :
    ∀ (n : ℕ) (F : Polynomial V), F.Monic → F.natDegree = n →
      ∃ s : Multiset V, F = (s.map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro n
  induction n with
  | zero =>
    intro F hF hdeg
    refine ⟨0, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact Polynomial.eq_one_of_monic_natDegree_zero hF hdeg
  | succ n ih =>
    intro F hF hdeg
    have hm : (F.map (algebraMap V (FractionRing V))).Monic := hF.map _
    have hnd : (F.map (algebraMap V (FractionRing V))).natDegree = n + 1 := by
      rw [hF.natDegree_map, hdeg]
    have hd0 : (F.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnd] at h
      norm_cast at h
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd0
    have hint : IsIntegral V x := ⟨F, hF, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx⟩
    obtain ⟨α, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hroot : F.IsRoot α := by
      apply IsFractionRing.injective V (FractionRing V)
      rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
      rw [hx, map_zero]
    have hmul : (Polynomial.X - Polynomial.C α) * (F /ₘ (Polynomial.X - Polynomial.C α)) = F :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hGm : (F /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C α) (by rw [hmul]; exact hF)
    have hGd : (F /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n := by
      rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C α), hdeg,
        Polynomial.natDegree_X_sub_C]
      omega
    obtain ⟨s, hs⟩ := ih _ hGm hGd
    refine ⟨α ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

private theorem coprime_left {R ι : Type} [CommRing R] (s : Multiset ι) (f : ι → R) (x : R)
    (h : ∀ a ∈ s, IsCoprime (f a) x) : IsCoprime (s.map f).prod x := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact isCoprime_one_left
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a t)).mul_left (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private theorem prod_notMem {R ι : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (s : Multiset ι) (f : ι → R) (h : ∀ a ∈ s, f a ∉ P) : (s.map f).prod ∉ P := by
  induction s using Multiset.induction_on with
  | empty =>
    intro h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using h1))
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    intro hm
    rcases hP.mem_or_mem hm with h1 | h1
    · exact h a (Multiset.mem_cons_self a t) h1
    · exact ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) h1

private theorem algebraMap_mem_maximal_of_mem_maximalIdeal (V : Type) [CommRing V] [IsLocalRing V] {A : Type} [CommRing A]
    [Algebra V A] [Algebra.IsIntegral V A] (m' : Ideal A) [m'.IsMaximal] {v : V}
    (hv : v ∈ IsLocalRing.maximalIdeal V) : algebraMap V A v ∈ m' := by
  have hc : (m'.comap (algebraMap V A)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V) m'
  rw [← IsLocalRing.eq_maximalIdeal hc] at hv
  exact hv

private theorem exists_idempotent_approx_at_maximal (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] {A : Type} [CommRing A] [Algebra V A] [Algebra.IsIntegral V A]
    (m : Ideal A) [hm : m.IsMaximal] (a : A) :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal A, m'.IsMaximal → e ∉ m' →
      ∃ β : V, a - algebraMap V A β ∈ m ∧ a - algebraMap V A β ∈ m' := by
  classical
  obtain ⟨F, hF, hFa⟩ := Algebra.IsIntegral.isIntegral (R := V) a
  obtain ⟨s, hs⟩ := split_monic V F.natDegree F hF rfl
  set f : V → A := fun α => a - algebraMap V A α with hf
  have hprod : (s.map f).prod = 0 := by
    have h0 : Polynomial.aeval a F = 0 := by
      rw [Polynomial.aeval_def]
      exact hFa
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    simpa [f, Function.comp_def] using h0
  set g := ((s.filter (fun α => f α ∈ m)).map f).prod with hg
  set h := ((s.filter (fun α => ¬ f α ∈ m)).map f).prod with hh
  have hgh : g * h = 0 := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not, hprod]
  have hhm : h ∉ m := prod_notMem m _ f (fun α hα => (Multiset.mem_filter.mp hα).2)
  have hgm : g ∈ m := by
    have hz : g * h ∈ m := by
      rw [hgh]
      exact m.zero_mem
    exact (hm.isPrime.mem_or_mem hz).resolve_right hhm
  have hcop : IsCoprime g h := by
    apply IsCoprime.symm
    apply coprime_left
    intro β hβ
    apply IsCoprime.symm
    apply coprime_left
    intro α hα
    have hPα : f α ∈ m := (Multiset.mem_filter.mp hα).2
    have hPβ : f β ∉ m := (Multiset.mem_filter.mp hβ).2
    have hu : IsUnit (α - β) := by
      by_contra hnu
      apply hPβ
      have hmem : algebraMap V A (α - β) ∈ m :=
        algebraMap_mem_maximal_of_mem_maximalIdeal V m ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      have hfe : f β = f α + algebraMap V A (α - β) := by
        simp only [f, map_sub]
        ring
      rw [hfe]
      exact m.add_mem hPα hmem
    obtain ⟨w, hw⟩ := hu
    refine ⟨-algebraMap V A (↑w⁻¹ : V), algebraMap V A (↑w⁻¹ : V), ?_⟩
    have hw1 : algebraMap V A (↑w⁻¹ : V) * algebraMap V A (α - β) = 1 := by
      rw [← map_mul, ← hw, Units.inv_mul, map_one]
    simp only [f, map_sub] at hw1 ⊢
    linear_combination hw1
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v * h, ?_, ?_, ?_⟩
  · show v * h * (v * h) = v * h
    linear_combination (v * h) * huv - (u * v) * hgh
  · intro he
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    exact m.add_mem (m.mul_mem_left u hgm) he
  · intro m' hm' he
    have hhm' : h ∉ m' := fun hh' => he (m'.mul_mem_left v hh')
    have hex : ∃ α ∈ s, f α ∈ m' := by
      by_contra hne
      push_neg at hne
      have hn := prod_notMem (hP := hm'.isPrime) m' s f hne
      rw [hprod] at hn
      exact hn m'.zero_mem
    obtain ⟨α, hαs, hαm'⟩ := hex
    by_cases hPα : f α ∈ m
    · exact ⟨α, hPα, hαm'⟩
    · exfalso
      apply hhm'
      have hmemf : α ∈ s.filter (fun α => ¬ f α ∈ m) := Multiset.mem_filter.mpr ⟨hαs, hPα⟩
      obtain ⟨c, hc⟩ := Multiset.dvd_prod (Multiset.mem_map_of_mem f hmemf)
      rw [hh, hc]
      exact m'.mul_mem_right c hαm'

theorem UpperTheory.Gal.Mod.hensSplit :
    HensSplit := by
  intro V _ _ _ _ A _ _ _ m hm
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := V) (M := A)
  choose E hEi hEm hEm' using fun t : A => exists_idempotent_approx_at_maximal V m t
  refine ⟨∏ t ∈ T, E t, ?_, ?_, ?_⟩
  · show (∏ t ∈ T, E t) * (∏ t ∈ T, E t) = ∏ t ∈ T, E t
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun t _ => (hEi t).eq)
  · rw [Finset.prod_eq_multiset_prod]
    exact prod_notMem m T.val E (fun t _ => hEm t)
  · intro m' hm' hne
    by_contra hem'
    have hall : ∀ t ∈ T, ∃ β : V, t - algebraMap V A β ∈ m ⊓ m' := by
      intro t ht
      have hEt : E t ∉ m' := by
        intro hE
        apply hem'
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem E ht
        rw [hc]
        exact m'.mul_mem_right c hE
      obtain ⟨β, h1, h2⟩ := hEm' t m' hm' hEt
      exact ⟨β, Ideal.mem_inf.mpr ⟨h1, h2⟩⟩
    have hspan : ∀ x : A, ∃ β : V, x - algebraMap V A β ∈ m ⊓ m' := by
      intro x
      have hx : x ∈ Submodule.span V (T : Set A) := by
        rw [hT]
        trivial
      induction hx using Submodule.span_induction with
      | mem y hy => exact hall y hy
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨β, hβ⟩ := hy
        obtain ⟨γ, hγ⟩ := hz
        refine ⟨β + γ, ?_⟩
        have hyz : y + z - algebraMap V A (β + γ) =
            (y - algebraMap V A β) + (z - algebraMap V A γ) := by
          rw [map_add (f := _)]
          ring
        rw [hyz]
        exact (m ⊓ m').add_mem hβ hγ
      | smul c y _ hy =>
        obtain ⟨β, hβ⟩ := hy
        refine ⟨c * β, ?_⟩
        have hcy : c • y - algebraMap V A (c * β) = algebraMap V A c * (y - algebraMap V A β) := by
          rw [Algebra.smul_def, map_mul]
          ring
        rw [hcy]
        exact (m ⊓ m').mul_mem_left _ hβ
    have hle : m ≤ m' := by
      intro x hx
      obtain ⟨β, hβ⟩ := hspan x
      have hβ1 := (Ideal.mem_inf.mp hβ).1
      have hβ2 := (Ideal.mem_inf.mp hβ).2
      have hβm : algebraMap V A β ∈ m := by
        have hd := m.sub_mem hx hβ1
        simpa using hd
      have hβmax : β ∈ IsLocalRing.maximalIdeal V := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hβm (hu.map _))
      have hs := m'.add_mem hβ2 (algebraMap_mem_maximal_of_mem_maximalIdeal V m' hβmax)
      simpa using hs
    exact hne (hm.eq_of_le hm'.ne_top hle).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PNwtOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

private theorem mem_basicOpen_of_ne {p : ℕ} {Y : Scheme.{0}} (Ω : Type) [Field Ω]
    (x : gp Ω ⟶ Y) (hp : (p : Ω) ≠ 0) : pt x ∈ Y.basicOpen (p : Γ(Y, ⊤)) := by
  have hu : IsUnit ((p : ℕ) : Γ(gp Ω, ⊤)) := by
    have h1 : IsUnit ((p : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hp
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    simpa using h2
  have h3 : (gp Ω).basicOpen (x.appTop (p : Γ(Y, ⊤))) = ⊤ := by
    rw [map_natCast]
    exact Scheme.basicOpen_of_isUnit _ hu
  have h4 : IsLocalRing.closedPoint Ω ∈ x ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h3]
    trivial
  exact h4

theorem nwtOne : NwtOne := by
  intro p Y T hL _
  obtain ⟨_, _, _, _, _, _, _, hMB, _, _, hWN, _, hNF, _, _⟩ := all_holds.1
  haveI := T.fin
  have hN : IsNwt T.p (nwt T.p) := hWN T.p hL
  refine ⟨hN.1, ?_⟩
  intro Ω _ _ z hp
  haveI := T.et
  have hD : Dense {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} := by
    have hs : {s | GenPt ((Y.basicOpen (p : Γ(Y, ⊤))).ι s)} =
        {s | GenPt s} := by
      ext s
      exact genBasic_of.2.1 (Y.basicOpen (p : Γ(Y, ⊤))).ι s
    rw [hs]
    exact genBasic_of.1 _
  have hc := hNF (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤))) T.p
    (Y.basicOpen (p : Γ(Y, ⊤))).ι (isPullback_morphismRestrict T.p _).flip hN hD
  rw [hMB.2.2 (T.p ∣_ Y.basicOpen (p : Γ(Y, ⊤)))] at hc
  have hmem : pt (z ≫ T.p) ∈ Y.basicOpen (p : Γ(Y, ⊤)) := mem_basicOpen_of_ne Ω (z ≫ T.p) hp
  have hr : Set.range z ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hq
    exact hmem
  have hz := IsOpenImmersion.lift_fac (T.p ⁻¹ᵁ Y.basicOpen (p : Γ(Y, ⊤))).ι z hr
  have h5 := congrArg (fun w : Wt _ => w Ω (IsOpenImmersion.lift _ z hr)) hc
  simp only [Wt.comap, hz] at h5
  rw [h5]
  rfl

end UpperTheory.Gal.Mod

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.POpCover
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem push_const_one {Z Z' : Scheme.{0}} (u : Z ⟶ Z') [IsFinite u] (δ : ℕ)
    (hδ : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Z'), (fib u x).ncard = δ) :
    (Wt.const Z 1).push u = Wt.const Z' (δ : ℤ) := by
  funext Ω _ _ x
  simp only [Wt.push, Wt.const]
  rw [← hδ Ω x]
  obtain hs | hs := (fib u x).infinite_or_finite
  · rw [hs.ncard, Nat.cast_zero]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hs)
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card _ hs]
    simp

theorem UpperTheory.Gal.Mod.opCover :
    OpCover := by
  intro l _ S S' c c' u _ δ hw hw' hp hf hl hδ k i
  haveI := c.fin
  haveI := c'.fin
  have hadic := TranscendenceTraces.all_holds.2.2
  have hwl := TranscendenceTraces.all_holds.1.2.2.1
  have hwc : IsWt (u ≫ c'.p) (Wt.const c.Z 1) := by
    have h0 := c.wt
    rw [hw, ← hp] at h0
    exact h0
  have hwc' : IsWt c'.p (Wt.const c'.Z 1) := by
    have h0 := c'.wt
    rw [hw'] at h0
    exact h0
  have hpush := TranscendenceTraces.trPushQ_of TranscendenceTraces.trPush_holds hadic.2.1 TranscendenceTraces.wtPush_holds l k i u c'.p
    (Wt.const c.Z 1) hwc hl
  rw [push_const_one u δ hδ] at hpush
  have hcomp := hadic.2.2.2.1 l k i c'.p (𝟙 S) (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) hwc'
    (hwl.2.2 (𝟙 S) (δ : ℤ)) hl
  have hmul : Wt.mul c'.p (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) = Wt.const c'.Z (δ : ℤ) := by
    funext Ω _ _ z
    simp [Wt.mul, Wt.const]
  rw [Category.comp_id, hmul, TranscendenceTraces.trIdQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance l k i S δ hl,
    LinearMap.smul_comp, LinearMap.id_comp] at hcomp
  have hpull : pullHQ l (sch.map (u ≫ c'.f)) k i =
      pullHQ l (sch.map u) k i ∘ₗ pullHQ l (sch.map c'.f) k i := by
    simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
  unfold TranscendenceTraces.Corr.opQ
  rw [← hf, ← hp, hw, hw', hpull, ← LinearMap.comp_assoc, hpush, hcomp, LinearMap.smul_comp]
  first
    | rfl
    | simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    | (norm_cast; simp [Nat.cast_smul_eq_nsmul])
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSecGen
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.secGen :
    SecGen := by
  intro Z Y g _ V _ _ _ y
  have hP : IsProper g := inferInstance
  have hV : ValuativeCriterion g := by
    rw [IsProper.eq_valuativeCriterion] at hP
    exact hP.1.1.1
  let e : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    show (e ≫ z) ≫ g = e ≫ y
    rw [Category.assoc, show z ≫ g = y from hz]
  · intro z₁ hz₁ z₂ hz₂ h
    have h₁ : z₁ ≫ g = y := hz₁
    have h₂ : z₂ ≫ g = y := hz₂
    have h' : e ≫ z₁ = e ≫ z₂ := h
    let S : ValuativeCommSq g :=
      ⟨V, FractionRing V, e ≫ z₁, y, ⟨by rw [Category.assoc, h₁]⟩⟩
    have hu := ValuativeCriterion.uniqueness hV S
    have := @Subsingleton.elim _ hu
      ⟨z₁, rfl, h₁⟩ ⟨z₂, h'.symm, h₂⟩
    exact congrArg CommSq.LiftStruct.l this
  · intro x hx
    have hx' : x ≫ g = e ≫ y := hx
    let S : ValuativeCommSq g := ⟨V, FractionRing V, x, y, ⟨hx'⟩⟩
    obtain ⟨⟨l⟩⟩ := ValuativeCriterion.existence hV S
    exact ⟨l.l, l.fac_right, l.fac_left⟩
end

