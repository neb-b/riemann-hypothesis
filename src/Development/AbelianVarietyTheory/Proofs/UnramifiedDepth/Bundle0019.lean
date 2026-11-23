module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.Bundle0023
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesCoeffMulLe
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LocalFactorModPNilOver
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

open TensorProduct IsLocalRing Matrix in
private theorem exists_localFactor_lemma {R₀ : Type} [CommRing R₀] {O R K A : _root_.ReciprocityTheory.PGsh.LAlg R₀}
    (q : _root_.ReciprocityTheory.PGsh.LHom O R) (hq : Function.Surjective q.1) (c : O.carrier)
    (hker : RingHom.ker (q.1 : O.carrier →+* R.carrier) = Ideal.span {c})
    (ρ : _root_.ReciprocityTheory.PGsh.LHom R K) (hρ : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρ) (hK : maximalIdeal K.carrier = ⊥)
    (s : _root_.ReciprocityTheory.PGsh.LHom O A) (hfin : (s.1 : O.carrier →+* A.carrier).Finite)
    (φ₀ : _root_.ReciprocityTheory.PGsh.LHom A O) (hφ₀ : φ₀.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O) :
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom A Λ) (j : _root_.ReciprocityTheory.PGsh.LHom R Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = ρ ∧ μ.comp s = j.comp q ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ R, ψ.comp μ = q.comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id R ∧ ρ.comp ψ = ρΛ := by
  classical
  have hmR : ∀ x ∈ maximalIdeal R.carrier, IsNilpotent x := by
    intro x hx
    apply hρ.2
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) x ∈ maximalIdeal K.carrier := map_nonunit _ x hx
    rw [hK] at h1
    exact h1
  have hc0 : q.1 c = 0 := by
    have h1 : c ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := hker ▸ Ideal.mem_span_singleton_self c
    exact h1
  have hc : ¬ IsUnit c := by
    intro hu
    have h1 := hu.map q.1
    rw [hc0] at h1
    exact not_isUnit_zero h1
  have hsc : ¬ IsUnit (s.1 c) := by
    haveI := s.2
    exact fun h => hc ((isUnit_map_iff (s.1 : O.carrier →+* A.carrier) c).1 h)
  set I : Ideal A.carrier := Ideal.span {s.1 c} with hI
  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]
    exact hsc
  haveI : Nontrivial (A.carrier ⧸ I) := _root_.ReciprocityTheory.PGsh.Ainf.quot_nontrivial I hItop
  haveI : IsLocalRing (A.carrier ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀ := _root_.ReciprocityTheory.PGsh.LAlg.mk (A.carrier ⧸ I)
  let μ : _root_.ReciprocityTheory.PGsh.LHom A Λ := ⟨Ideal.Quotient.mkₐ R₀ I,
    _root_.ReciprocityTheory.PGsh.TowerExample.isLocalHom_of_surj ((Ideal.Quotient.mkₐ R₀ I : A.carrier →ₐ[R₀] A.carrier ⧸ I) : A.carrier →+* A.carrier ⧸ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I)⟩
  have hqc : ∀ a ∈ RingHom.ker q.1, ((Ideal.Quotient.mkₐ R₀ I).comp s.1) a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := ha
    rw [hker, Ideal.mem_span_singleton'] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [AlgHom.comp_apply, map_mul, map_mul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero]
  let j₀ : R.carrier →ₐ[R₀] A.carrier ⧸ I :=
    (Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc).comp
      (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hj₀ : ∀ x, j₀ (q.1 x) = Ideal.Quotient.mk I (s.1 x) := by
    intro x
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x) =
        Ideal.Quotient.mk (RingHom.ker q.1) x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc
      ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x)) = _
    rw [h1]
    rfl
  have hj₀loc : IsLocalHom (j₀ : R.carrier →+* A.carrier ⧸ I) := by
    constructor
    intro x hx
    by_contra hxu
    obtain ⟨n, hn⟩ := hmR x ((mem_maximalIdeal x).2 hxu)
    have h1 : IsUnit ((j₀ : R.carrier →+* A.carrier ⧸ I) x ^ n) := hx.pow n
    rw [← map_pow, hn, map_zero] at h1
    exact not_isUnit_zero h1
  let j : _root_.ReciprocityTheory.PGsh.LHom R Λ := ⟨j₀, hj₀loc⟩
  have hψI : ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → ∀ a ∈ I, (q.1.comp φ.1) a = 0 := by
    intro φ hφ a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    have h1 : φ.1 (s.1 c) = c := congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O O => f.1 c) hφ
    rw [AlgHom.comp_apply, map_mul, map_mul, h1, hc0, mul_zero]
  let ψ₀ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → (A.carrier ⧸ I →ₐ[R₀] R.carrier) :=
    fun φ hφ => Ideal.Quotient.liftₐ I (q.1.comp φ.1) (hψI φ hφ)
  have hψ₀mk : ∀ φ hφ a, ψ₀ φ hφ (Ideal.Quotient.mk I a) = q.1 (φ.1 a) := fun _ _ _ => rfl
  have hψ₀loc : ∀ φ hφ, IsLocalHom (ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) := by
    intro φ hφ
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : IsUnit (q.1 (φ.1 a)) := hx
    haveI := q.2
    haveI := φ.2
    have h2 : IsUnit (φ.1 a) := isUnit_of_map_unit (q.1 : O.carrier →+* R.carrier) _ h1
    have h3 : IsUnit a := isUnit_of_map_unit (φ.1 : A.carrier →+* O.carrier) _ h2
    exact h3.map (Ideal.Quotient.mk I)
  let ψ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → _root_.ReciprocityTheory.PGsh.LHom Λ R :=
    fun φ hφ => ⟨ψ₀ φ hφ, hψ₀loc φ hφ⟩
  have hψj : ∀ φ hφ r, ψ₀ φ hφ (j₀ r) = r := by
    intro φ hφ r
    obtain ⟨x, rfl⟩ := hq r
    rw [hj₀, hψ₀mk φ hφ]
    exact congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O R => f.1 x)
      (show q.comp (φ.comp s) = q.comp (_root_.ReciprocityTheory.PGsh.LHom.id O) by rw [hφ])
  have hkerm : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = 0 →
      l ∈ maximalIdeal (A.carrier ⧸ I) := by
    intro φ hφ l hl
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (ρ.1 (ψ₀ φ hφ l)) := (hu.map (ψ₀ φ hφ)).map ρ.1
    rw [hl] at h1
    exact not_isUnit_zero h1
  have hmK : ∀ φ hφ (l : A.carrier ⧸ I), l ∈ maximalIdeal (A.carrier ⧸ I) →
      ρ.1 (ψ₀ φ hφ l) = 0 := by
    intro φ hφ l hl
    haveI := hψ₀loc φ hφ
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) ((ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) l) ∈
        maximalIdeal K.carrier :=
      map_nonunit _ _ (map_nonunit _ l hl)
    rw [hK] at h1
    exact h1
  have hagree : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = ρ.1 (ψ₀ φ₀ hφ₀ l) := by
    intro φ hφ l
    have h1 : ρ.1 (ψ₀ φ₀ hφ₀ (l - j₀ (ψ₀ φ₀ hφ₀ l))) = 0 := by
      rw [map_sub, hψj φ₀ hφ₀ (ψ₀ φ₀ hφ₀ l), sub_self, map_zero]
    have h2 := hmK φ hφ _ (hkerm φ₀ hφ₀ _ h1)
    rw [map_sub, map_sub, hψj φ hφ (ψ₀ φ₀ hφ₀ l), sub_eq_zero] at h2
    exact h2
  have hcomp : (Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier) =
      (j₀ : R.carrier →+* A.carrier ⧸ I).comp (q.1 : O.carrier →+* R.carrier) := by
    ext x
    exact (hj₀ x).symm
  have hint : ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier)).IsIntegral :=
    ((RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).comp
      hfin).to_isIntegral
  refine ⟨Λ, μ, j, ρ.comp (ψ φ₀ hφ₀), ⟨fun k => ?_, fun l hl => ?_⟩,
    Ideal.Quotient.mkₐ_surjective R₀ I, ?_, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hρ.1 k
    refine ⟨j₀ r, ?_⟩
    show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
    rw [hψj φ₀ hφ₀ r]
  · have hl' : ρ.1 (ψ₀ φ₀ hφ₀ l) = 0 := hl
    have hm := hkerm φ₀ hφ₀ l hl'
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJR : J.comap (j₀ : R.carrier →+* A.carrier ⧸ I) = maximalIdeal R.carrier := by
      have hP : (J.comap (j₀ : R.carrier →+* A.carrier ⧸ I)).IsPrime := Ideal.comap_isPrime _ J
      apply le_antisymm
      · exact le_maximalIdeal hP.ne_top
      · intro x hx
        obtain ⟨n, hn⟩ := hmR x hx
        exact hP.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
    have hmax : (J.comap ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier))).IsMaximal := by
      rw [hcomp, ← Ideal.comap_comap, hJR]
      exact Ideal.comap_isMaximal_of_surjective (q.1 : O.carrier →+* R.carrier) hq
    have hJmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hint J hmax
    rw [eq_maximalIdeal hJmax]
    exact hm
  · exact Subtype.ext (AlgHom.ext fun r => by
      show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
      rw [hψj φ₀ hφ₀ r])
  · exact Subtype.ext (AlgHom.ext fun x => by
      show Ideal.Quotient.mk I (s.1 x) = j₀ (q.1 x)
      exact (hj₀ x).symm)
  · intro φ hφ
    refine ⟨ψ φ hφ, Subtype.ext (AlgHom.ext fun a => rfl),
      Subtype.ext (AlgHom.ext fun r => hψj φ hφ r), Subtype.ext (AlgHom.ext fun l => hagree φ hφ l)⟩


open TensorProduct IsLocalRing Matrix in
theorem _root_.GlobalTheory.localFactor_mod_p_nilOver :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Λ) (j : _root_.ReciprocityTheory.PGsh.LHom (Tw.R 0) Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ D.K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D hg
  have hid : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver (_root_.ReciprocityTheory.PGsh.LHom.id D.K) :=
    ⟨fun x => ⟨x, rfl⟩, fun a ha => ⟨1, by rw [pow_one]; exact (RingHom.mem_ker).1 ha⟩⟩
  have hK : maximalIdeal (D.K : Type) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hsub : ∀ u v : {x // (B.map (_root_.ReciprocityTheory.PGsh.LHom.id D.K)) x = 0}, u = v := by
      intro u v
      have hu := u.2
      have hv := v.2
      rw [B.map_id] at hu hv
      exact Subtype.ext (hu.trans hv.symm)
    have h1 : (fun _ : Fin g => (⟨a, ha⟩ : maximalIdeal (D.K : Type))) = fun _ => 0 :=
      (D.ch.χ (_root_.ReciprocityTheory.PGsh.LHom.id D.K) hid).symm.injective (hsub _ _)
    have h2 := congrFun h1 ⟨0, hg⟩
    exact (Ideal.mem_bot).2 (congrArg Subtype.val h2)
  have hW := D.sm.nil
  have heq := D.wd.ρW_eq
  have hρ1 : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 := by
    refine ⟨fun k => ?_, fun a ha => ?_⟩
    · obtain ⟨w, hw⟩ := hW.1 k
      refine ⟨D.wd.πW.1 w, ?_⟩
      rw [← hw, ← heq]
      rfl
    · obtain ⟨w, rfl⟩ := D.wd.πW_surj a
      have hw : w ∈ RingHom.ker (D.wd.ρW.1 : D.wd.W.carrier →+* D.K.carrier) := by
        rw [RingHom.mem_ker, ← heq]
        exact (RingHom.mem_ker).1 ha
      exact (hW.2 w hw).map (D.wd.πW.1 : D.wd.W.carrier →+* (Tw.R 0).carrier)
  refine ⟨hK, hρ1, fun i => ?_⟩
  have hsec : ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : (D.fin.AAx i).carrier) = 0 := D.fin.sep i 1 fun φ hφ => absurd hφ (hne φ)
    exact one_ne_zero h1
  obtain ⟨φ₀, hφ₀⟩ := hsec
  have hfin : ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).Finite := by
    letI : Algebra Tw.O.carrier (D.fin.AAx i).carrier :=
      ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
    exact (D.fin.free i).2
  exact exists_localFactor_lemma (Tw.q 0) D.tower_zero_surjective (p : Tw.O.carrier) D.tower_zero_ker D.wd.ρ1 hρ1 hK
    (D.fin.sO i) hfin φ₀ hφ₀

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesLeafMainTermCurveSystem
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

open Formalism.BaseCaseIdentities (Data Kn s0)

theorem zetaSeries_main_term_fintype (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (l : ℕ) (hl : l.Prime) (hv : v (l : C) = 1) (h3 : 3 ≤ l) (I : Type) [Fintype I] (M s₀ : ℕ)
    (good : I → Prop) (Gs : ℕ → Finset I) (al : I → ℕ → I → C) (π : ℕ → I → Fin M → C)
    (t : I → MvPowerSeries (Fin M) C) (h1 : ∀ s c, c ∈ Gs s → good c)
    (h2 : ∀ s s' c, c ∈ Gs s → c ∈ Gs s' → s = s')
    (h4 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (h5 : ∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h6 : ∀ c, good c → ∀ e, al c 1 e = 0)
    (h6' : ∀ c, good c → ∀ (n : ℕ) e, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e))
    (h7 : ∀ s < s₀, ∀ c ∈ Gs s, ∀ e, e ∉ Gs (s + 1) → 0 ≤ v (al c 2 e))
    (h8 : ∀ c j, 0 ≤ v (π 0 c j)) (h9 : ∀ c, c ∉ Gs 0 → ∀ j, π 0 c j = 0)
    (h10 : ∀ s e j, π (s + 1) e j = ∑ c ∈ Gs s, (l : C) * al c 2 e * π s c j ^ (l ^ 2))
    (h11 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (h12 : ∀ (e : I) (μ : Fin M →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c,
      al c s e * MvPowerSeries.coeff μ (t c ^ (l ^ s)) =
        MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (π 0 e j) *
          (MvPowerSeries.X j : MvPowerSeries (Fin M) C)))
    (be : I → ℕ → C) (h13 : ∀ c, be c 0 = 0)
    (h14 : ∀ c (n : ℕ), ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h15 : ∀ c, good c → ∀ n : ℕ, 2 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (be c n))
    (h16 : ∀ s < s₀, ∀ c ∈ Gs s, be c 1 = 0) (ζ : MvPowerSeries (Fin M) C)
    (h17 : ∀ α, MvPowerSeries.coeff α ζ = -∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ c,
      be c n * MvPowerSeries.coeff α (t c ^ (l ^ n))) :
    ReciprocityTheory.PGsh.OrdGe v (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ (2 * s₀ + 1)))
      (ζ - ∑ j, MvPowerSeries.C (R := C)
        (((l : C) ^ (1 + l * (∑ u ∈ Finset.range s₀, (l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s₀ + 1) * ∑ c ∈ Gs s₀, π s₀ c j ^ l * ((l : C) * be c 1))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (l ^ (2 * s₀ + 1))) 0 := by
  let φ : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hmem : ∀ s c, c ∈ (Gs s).map φ.toEmbedding ↔ φ.symm c ∈ Gs s := fun s c =>
    Finset.mem_map_equiv
  have key := GlobalTheory.zetaSeries_main_term C v l hl hv h3 (Fintype.card I) M s₀ {c | good (φ.symm c)}
    (fun s => (Gs s).map φ.toEmbedding) (fun c n e => al (φ.symm c) n (φ.symm e))
    (fun s e j => π s (φ.symm e) j) (fun c => t (φ.symm c))
    (fun s c hc => h1 s _ ((hmem s c).1 hc))
    (fun s s' c _ _ hc hc' => h2 s s' _ ((hmem s c).1 hc) ((hmem s' c).1 hc'))
    (fun c e => by simp [h4])
    (fun c n e => h5 _ n _)
    (fun c hc => ⟨funext fun e => h6 _ hc _, fun n e hn => h6' _ hc n _ hn⟩)
    (fun s hs c hc e he => h7 s hs _ ((hmem s c).1 hc) _ (fun h => he ((hmem _ e).2 h)))
    (fun c j => h8 _ j)
    (fun c hc => funext fun j => h9 _ (fun h => hc ((hmem _ c).2 h)) j)
    (fun s e j => by simp [h10, Finset.sum_map])
    (fun c => h11 _)
    (fun e => by
      ext μ
      rw [← h12 (φ.symm e) μ]
      change ∑ n ∈ Finset.range (μ.degree + 1), ∑ a, al (φ.symm a) n (φ.symm e) *
        MvPowerSeries.coeff μ (t (φ.symm a) ^ (l ^ n)) = _
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Equiv.sum_comp φ.symm (fun c => al c n (φ.symm e) * MvPowerSeries.coeff μ (t c ^ (l ^ n))))
    1 (fun c n _ => be (φ.symm c) n) 0
    (fun c => h13 _) (fun c n => h14 _ n) (fun c hc n hn => h15 _ hc n hn)
    (fun s hs c hc => h16 s hs _ ((hmem s c).1 hc)) ζ
    (fun α => by
      rw [h17 α]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      exact (Equiv.sum_comp φ.symm (fun c => be c n * MvPowerSeries.coeff α (t c ^ (l ^ n)))).symm)
  simpa only [Finset.sum_map, Equiv.coe_toEmbedding, Equiv.symm_apply_apply] using key

theorem zeta_leaf_main_term : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
  intro C _ _ V d _ I J _ _ G S Z D a i h hid t ht N em hem κ hκ
  have hDv : D.v = V.v := h.1
  have hDl : D.l = V.l := h.2.1
  have hDi : D.i = i := h.2.2.1
  have hi : Odd i := hDi ▸ D.i_odd
  have h3 : 3 ≤ V.l := hDl ▸ D.l_ge
  have hK : Kn i = s0 i + 1 := Kn_eq hi
  have hs : 2 * s0 i + 1 = i := two_mul_chainStartIndex_add_one_of_odd hi
  let al : I → ℕ → I → C := fun c k b => if k = 0 then (if c = b then 1 else 0) else D.al c k b
  have hal0 : ∀ c b, al c 0 b = if c = b then 1 else 0 := fun c b => by simp [al]
  have halk : ∀ c k b, 1 ≤ k → al c k b = D.al c k b := fun c k b hk => by
    have : k ≠ 0 := by omega
    simp [al, this]
  obtain ⟨hc1, hc2, hc3⟩ := GlobalTheory.MainTerm.linPull_coords C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => chainMat D 0 b (em j)) al
    (fun j x => by simp [chainMat_zero])
    (fun c b => by rw [hal0])
    (fun c k x hk => by
      rw [h.2.2.2.1 c k x hk]
      exact Finset.sum_congr rfl fun b _ => by rw [halk c k b hk])
  have hGs : ∀ s c, c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i) ↔
      D.lev c = s ∧ s < Kn D.i := fun s c => by simp
  have hl0 : (D.l : C) ≠ 0 := by exact_mod_cast D.l_prime.ne_zero
  have key := zetaSeries_main_term_fintype C V.v V.l V.l_prime V.v_l h3 I N (s0 i) D.good
    (fun s => Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i)) al
    (fun s e j => chainMat D s e (em j)) (fun c => linPull (fun δ => S.tan (em δ)) (t c))
    (fun s c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      exact D.pure_good c (h1 ▸ h2))
    (fun s s' c hc hc' => ((hGs s c).1 hc).1.symm.trans ((hGs s' c).1 hc').1)
    hal0
    (fun c n e => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hal0]
        split_ifs <;> simp
      · rw [halk c n e hn, ← hDv]
        exact D.al_all c n e)
    (fun c hc e => by rw [halk c 1 e le_rfl, D.al_one c hc])
    (fun c hc n e hn => by
      rw [halk c n e hn, ← hDv]
      have := D.al_good c hc n e hn
      rwa [neg_sub] at this)
    (fun s hs' c hc e he => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      have h4 : s + 1 < Kn D.i := by rw [hDi, hK]; omega
      have h5 : D.lev e ≠ D.lev c + 1 := fun h6 => he ((hGs _ e).2 ⟨by rw [h6, h1], h4⟩)
      rw [halk c 2 e (by norm_num), D.al_two c (h1 ▸ h2), D.g_supp c (h1 ▸ h4) e h5, zero_add,
        inv_mul_cancel_left₀ hl0, ← hDv]
      exact D.lam_int c e)
    (fun c j => by simpa [VF.Ge] using h.chainMat_int 0 c (em j))
    (fun c hc j => by
      rw [chainMat_zero, if_neg]
      rintro rfl
      exact hc ((hGs _ _).2 ⟨hem j, by rw [hDi, hK]; omega⟩))
    (fun s e j => by
      rw [chainMat_succ, hDl]
      exact Finset.sum_congr rfl fun c _ => by rw [halk c 2 e (by norm_num)])
    hc1 hc2 (fun c n => S.be c n κ) (fun c => S.be_zero c κ)
    (fun c n => G.bound0 n _ (S.mem c) (Sum.inr κ))
    (fun c hc n hn => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      have := (h.good hc).bound m (Sum.inr κ)
      have e : (1 - ((m + 2 : ℕ) : ℝ)) = -((m : ℝ) + 1) := by push_cast; ring
      rw [e]
      exact this)
    (fun s hs' c hc => by
      obtain ⟨h1, h2⟩ := (hGs s c).1 hc
      apply S.pure c 1
      rw [hκ, h.2.2.2.2 c (by rw [h1, ← hDi]; exact h2), h1, add_assoc, ← Nat.cast_add]
      intro h5
      have h6 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (add_left_cancel h5)
      rw [Nat.mod_eq_of_lt hid, Nat.mod_eq_of_lt (by omega)] at h6
      omega)
    (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) (hc3 κ)
  have hE : expE V.l i = 1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u) := rfl
  have hmain : ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ •
      (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i) =
      ∑ j, MvPowerSeries.C (R := C)
        (((V.l : C) ^ (1 + V.l * (∑ u ∈ Finset.range (s0 i), (V.l ^ 2) ^ u)))⁻¹ *
          ((-1) ^ (s0 i + 1) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s0 i ∧ s0 i < Kn D.i),
            chainMat D (s0 i) c (em j) ^ V.l * ((V.l : C) * S.be c 1 κ))) *
        (MvPowerSeries.X j : MvPowerSeries (Fin N) C) ^ (V.l ^ (2 * s0 i + 1)) := by
    rw [Finset.smul_sum, hs, hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, MvPowerSeries.smul_eq_C_mul, mainVec, hDl, hDi]
  rw [hmain]
  intro μ
  have hk := key μ
  rw [hs] at hk
  have hr : ∑ m, (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) * (μ m : ℝ) =
      (μ.degree : ℝ) * (r1 V.l i - del V.l i) := by
    rw [← Finset.mul_sum, Finsupp.degree_eq_sum, Nat.cast_sum, mul_comm]
    congr 1
    unfold r1 del rho
    have : (V.l : ℝ) ≠ 0 := by exact_mod_cast V.l_prime.ne_zero
    rw [add_sub_assoc]
    congr 1
    field_simp
    ring
  simp only [hr] at hk
  rw [hs]
  calc (((0 : ℝ) : ℝ) : WithTop ℝ)
      = ((0 - (μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) +
        (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, sub_add_cancel]
    _ ≤ _ := add_le_add_left hk _

end GlobalTheory.MainTerm
end
end

