module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0005
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0007
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.CorrespondenceNormBoundOfAffineOpens
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private lemma spec_chart {B : Type} [CommRing B] {X : Scheme.{0}} (w : Spec (CommRingCat.of B) ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    w = Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) ≫ hV.fromSpec := by
  rw [Spec.map_comp, Category.assoc, hV.SpecMap_appLE_fromSpec w (isAffineOpen_top _) hw,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

private lemma unit_away (l : ℕ) (B : Type) [CommRing B] :
    IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : B))), ⊤)) := by
  have h : IsUnit (l : Localization.Away (l : B)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : B)))).inv.hom

private lemma chart_norm {l Q n : ℕ} {Y : Scheme.{0}} (T : Fin (n + 1) → Corr l Y) {U V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) (π : Γ(Y, ⊤))
    (hn : NormOn l Q n π T U V h) (B : Type) [CommRing B] (hl : (l : B) ∈ nonZeroDivisors B)
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (z : ∀ j, Fin (T j).d → (Spec (CommRingCat.of B) ⟶ (T j).Z)) (hzy : ∀ j i, z j i ≫ (T j).p = y)
    (hs : ∀ j, SplitOn (T j).p (awayPt l B ≫ y) fun i => awayPt l B ≫ z j i)
    (B' : Type) [CommRing B'] (ψ : B →+* B')
    (hψ : ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (y.appTop.hom π)) = 0) :
    ∃ α : ∀ j, Fin (T j).d → (Γ(Y, V) →+* B),
      (∀ j i, z j i ≫ (T j).r = ptOf hV B (α j i)) ∧
      ∀ (ι : Type) [Fintype ι] (x : ι → Γ(Y, V)),
        SameNorm (pts (wEv Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j))
          (pts (wOd Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j)) := by
  have hz : ∀ j i, ⊤ ≤ z j i ⁻¹ᵁ ((T j).p ⁻¹ᵁ U) := fun j i => by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hy
  letI := fun j => (T j).alg U
  letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
  have H := fun j => splitRules.2 l Y (T j) U hU B y hy (z j) (hz j) (hzy j) (hs j)
  choose ζ hζ hζe using H
  have hres : ψ (algebraMap Γ(Y, U) B (Y.presheaf.map (homOfLE le_top).op π)) = 0 := by
    have e : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ y.appLE U ⊤ hy = y.appTop := by
      rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e' : algebraMap Γ(Y, U) B (Y.presheaf.map (homOfLE le_top).op π) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (y.appTop.hom π) := by
      rw [← e]
      rfl
    rw [e', hψ]
  refine ⟨fun j i => (ζ j i).toRingHom.comp ((T j).r.appLE V _ (h j)).hom, fun j i => ?_, fun ι _ x => ?_⟩
  · haveI := (T j).fin
    have hS : IsAffineOpen ((T j).p ⁻¹ᵁ U) := hU.preimage (T j).p
    have e1 := spec_chart (z j i) hS (hz j i)
    have e2 : (z j i).appLE ((T j).p ⁻¹ᵁ U) ⊤ (hz j i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        CommRingCat.ofHom (ζ j i).toRingHom := by
      ext a
      exact (hζe j i a).symm
    rw [e2] at e1
    have e3 := (ptChart_of Y V hV B).2.2 (T j).Z (T j).r _ hS (h j) B (RingHom.id B) (ζ j i).toRingHom
    have e4 : Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 _ := by
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [e4, Category.id_comp, RingHom.id_comp] at e3
    rw [e1]
    exact (Category.assoc _ _ _).trans e3
  · exact hn B hl (fun j => Fin (T j).d) ζ hζ B' ψ hres ι x

theorem UpperTheory.correspondence_norm_bound_of_affine_opens :
    ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (ϖ : O) (Q n : ℕ)
        (T : Fin (n + 1) → Corr l Y) (κ : O →+* OC l) (D : WDat l T)
        (A : Test l) (y : (PX (D.π ≫ q) κ).obj A.obj) {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
        (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V), ⊤ ≤ (y.1 ≫ D.π) ⁻¹ᵁ U →
        NormOn l Q n (fn q ϖ) T U V h → ∀ (ψ : A.obj.U →+* Qb A.obj), ψ (A.obj.oC (κ ϖ)) = 0 →
        ∃ α : ∀ j, Fin (T j).d → (Γ(Y, V) →+* A.obj.U),
          (∀ j i, y.1 ≫ D.s j i ≫ (T j).r = ptOf hV A.obj.U (α j i)) ∧
          ∀ (ι : Type) [Fintype ι] (x : ι → Γ(Y, V)),
            SameNorm (pts (wEv Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j))
              (pts (wOd Q) fun j i k => ψ (α j i (x k)) ^ Q ^ (n - j)) := by
  intro l _ O _ Y q ϖ Q n T κ D A y U V hU hV h hy hn ψ hψ
  have hl : (l : A.obj.U) ∈ nonZeroDivisors A.obj.U := (testFacts l A.obj A.property).1
  have hyq : (y.1 ≫ D.π) ≫ q = Spec.map (CommRingCat.ofHom (A.obj.oC.comp κ)) := by
    rw [Category.assoc]
    exact y.2
  have hval : (Scheme.ΓSpecIso (CommRingCat.of A.obj.U)).hom.hom ((y.1 ≫ D.π).appTop.hom (fn q ϖ)) =
      A.obj.oC (κ ϖ) := by
    have e : (y.1 ≫ D.π).appTop.hom (fn q ϖ) =
        ((y.1 ≫ D.π) ≫ q).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := by
      rw [Scheme.Hom.comp_appTop]
      rfl
    rw [e, hyq]
    have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (A.obj.oC.comp κ))
    have e3 := congr($(e2).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ))
    refine e3.trans ?_
    simp
  obtain ⟨α, h1, h2⟩ := chart_norm T hU hV h (fn q ϖ) hn A.obj.U hl (y.1 ≫ D.π) hy
    (fun j i => y.1 ≫ D.s j i) (fun j i => by rw [Category.assoc, D.hs])
    (fun j => by
      have := D.gen _ (awayPt l A.obj.U ≫ y.1) (unit_away l A.obj.U) j
      simpa only [Category.assoc] using this)
    (Qb A.obj) ψ (by rw [hval]; exact hψ)
  exact ⟨α, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.ExistsFiniteSectionsDeterminingRingHomOfSmooth
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

theorem UpperTheory.exists_finite_sections_determining_ringHom_of_smooth :
    ∀ {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)), Smooth q →
        ∀ {V : Y.Opens} (hV : IsAffineOpen V),
        ∃ (k : ℕ) (x : Fin k → Γ(Y, V)), ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
          ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂ := by
  intro O _ Y q hq V hV
  have hlft : LocallyOfFiniteType q := inferInstance
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of O)).Opens) := isAffineOpen_top _
  have hle : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hψ : (q.appLE ⊤ V hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q hlft ⟨⊤, htop⟩ ⟨V, hV⟩ hle
  let ι : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hι : Function.Surjective ι :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2
  let φ : O →+* Γ(Y, V) := (q.appLE ⊤ V hle).hom.comp ι
  have hφ : φ.FiniteType := hψ.comp (RingHom.FiniteType.of_surjective ι hι)
  letI : Algebra O Γ(Y, V) := φ.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, V) := hφ
  obtain ⟨s, hs⟩ := hft.out
  refine ⟨s.card, fun i => (s.equivFin.symm i : Γ(Y, V)), ?_⟩
  intro R _ f₁ f₂ hpt hgen
  have hcomp : f₁.comp (q.appLE ⊤ V hle).hom = f₂.comp (q.appLE ⊤ V hle).hom := by
    have e : ∀ f : Γ(Y, V) →+* R, ptOf hV R f ≫ q =
        Spec.map (CommRingCat.ofHom (f.comp (q.appLE ⊤ V hle).hom)) ≫ htop.fromSpec := by
      intro f
      unfold ptOf
      rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q htop hV hle, ← Category.assoc,
        ← Spec.map_comp]
      rfl
    rw [e, e] at hpt
    have h1 := Spec.map_injective ((cancel_mono htop.fromSpec).1 hpt)
    exact congrArg CommRingCat.Hom.hom h1
  have hO : ∀ a : O, f₁ (algebraMap O Γ(Y, V) a) = f₂ (algebraMap O Γ(Y, V) a) := fun a =>
    congrArg (fun g : Γ(Spec (CommRingCat.of O), ⊤) →+* R => g (ι a)) hcomp
  have hx : ∀ a ∈ s, f₁ a = f₂ a := fun a ha => by
    have := hgen (s.equivFin ⟨a, ha⟩)
    simpa using this
  ext a
  have ha : a ∈ Algebra.adjoin O (s : Set Γ(Y, V)) := by rw [hs]; trivial
  induction ha using Algebra.adjoin_induction with
  | mem b hb => exact hx b hb
  | algebraMap r => exact hO r
  | add b c _ _ hb hc => rw [map_add (f := _), map_add (f := _), hb, hc]
  | mul b c _ _ hb hc => rw [map_mul, map_mul, hb, hc]
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsLiftThroughSharp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

theorem UpperTheory.exists_orthogonalIdempotents_lift_through_sharp :
    ∀ (l : ℕ) [Fact l.Prime] (A : Test l) (I : Type) [Fintype I] (e : I → A.obj.U), CompleteOrthogonalIdempotents e →
        ∃ e₀ : I → A.obj.A, CompleteOrthogonalIdempotents e₀ ∧ ∀ i, A.obj.sharp (e₀ i) = e i := by
  intro l _ A I _ e he
  classical
  have hu : ∀ x : A.obj.U, IsIdempotentElem x → ∃! x₀ : A.obj.A, IsIdempotentElem x₀ ∧ A.obj.sharp x₀ = x :=
    (testFacts l A.obj A.property).2.2.2.2
  have s1 : A.obj.sharp 1 = 1 := map_one _
  have hsub : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp (1 - a) = 1 - A.obj.sharp a :=
    (CrystallineSemistableComparison.RL.sharp_cong A.obj).2.2
  have s0 : A.obj.sharp 0 = 0 := by
    have := hsub 1 IsIdempotentElem.one
    simpa [s1] using this
  have h := fun i => (hu (e i) (he.toOrthogonalIdempotents.idem i)).exists
  choose e₀ h1 h2 using h
  have hz : ∀ a : A.obj.A, IsIdempotentElem a → A.obj.sharp a = 0 → a = 0 := fun a ha hs =>
    (hu 0 IsIdempotentElem.zero).unique ⟨ha, hs⟩ ⟨IsIdempotentElem.zero, s0⟩
  have hort : ∀ i j, i ≠ j → e₀ i * e₀ j = 0 := fun i j hij =>
    hz _ ((h1 i).mul (h1 j)) (by
      rw [map_mul, h2, h2]
      exact he.toOrthogonalIdempotents.ortho hij)
  have hoi : OrthogonalIdempotents e₀ := ⟨h1, fun i j hij => hort i j hij⟩

  have hprod : ∀ s : Finset I, IsIdempotentElem (1 - ∑ i ∈ s, e₀ i) ∧
      ∀ i ∈ s, (1 - ∑ k ∈ s, e₀ k) * e₀ i = 0 := by
    intro s
    have hmul : ∀ i ∈ s, (∑ k ∈ s, e₀ k) * e₀ i = e₀ i := by
      intro i hi
      rw [Finset.sum_mul, Finset.sum_eq_single_of_mem i hi
        (fun k _ hk => hort k i hk)]
      exact h1 i
    have hsq : (∑ k ∈ s, e₀ k) * (∑ k ∈ s, e₀ k) = ∑ k ∈ s, e₀ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hmul
    refine ⟨?_, fun i hi => ?_⟩
    · change (1 - ∑ k ∈ s, e₀ k) * (1 - ∑ k ∈ s, e₀ k) = _
      linear_combination hsq
    · rw [sub_mul, one_mul, hmul i hi, sub_self]
  obtain ⟨t1, t2⟩ := hprod Finset.univ
  have ht : A.obj.sharp (1 - ∑ i, e₀ i) = 0 := by
    have hk : ∀ i, A.obj.sharp (1 - ∑ k, e₀ k) * e i = 0 := fun i => by
      rw [← h2 i, ← map_mul, t2 i (Finset.mem_univ i), s0]
    calc A.obj.sharp (1 - ∑ k, e₀ k) = A.obj.sharp (1 - ∑ k, e₀ k) * ∑ i, e i := by
          rw [he.complete, mul_one]
      _ = 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_eq_zero fun i _ => hk i
  have hsum : ∑ i, e₀ i = 1 := by
    have := hz _ t1 ht
    linear_combination -this
  exact ⟨e₀, ⟨hoi, hsum⟩, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsMatchingOfSameNorm
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private theorem powHom_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) :
    ∃ φ : A.A →+* A.A, ∀ x, φ x = x ^ l ^ a := by
  induction a with
  | zero => exact ⟨RingHom.id _, fun x => by simp⟩
  | succ a ih =>
    obtain ⟨φ, hφ⟩ := ih
    refine ⟨A.frob.comp φ, fun x => ?_⟩
    rw [RingHom.comp_apply, hφ, pow_succ l a, pow_mul]
    rfl

private theorem root_exists {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : ℕ) (y : A.A) :
    ∃ w : A.A, w ^ l ^ a = y := by
  induction a generalizing y with
  | zero => exact ⟨y, by simp⟩
  | succ a ih =>
    obtain ⟨z, hz⟩ := (A.perf.bijective_frobenius).2 y
    obtain ⟨w, hw⟩ := ih z
    refine ⟨w, ?_⟩
    rw [pow_succ l a, pow_mul, hw]
    exact hz

theorem UpperTheory.exists_orthogonalIdempotents_matching_of_sameNorm :
    ∀ (l : ℕ) [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ (a : ℕ) {ι I I' : Type} [Fintype ι] [Fintype I] [Fintype I']
        [DecidableEq I] [DecidableEq I'] (N : ℕ), Fintype.card I = N → Fintype.card I' = N →
        (N + 1) ^ N ≤ l ^ a → ∀ (c : I → ι → Qb A) (c' : I' → ι → Qb A),
        SameNorm (Finset.univ.val.map c) (Finset.univ.val.map c') →
        ∃ e : (I ≃ I') → A.A, CompleteOrthogonalIdempotents e ∧ ∀ σ i k,
          (Ideal.Quotient.mk _ (e σ) : Qb A) * c i k ^ l ^ a = Ideal.Quotient.mk _ (e σ) * c' (σ i) k ^ l ^ a := by
  intro l _ A hA a ι I I' _ _ _ _ _ N hI hI' hN c c' h
  have hq : 0 < l ^ a := pow_pos (Fact.out : l.Prime).pos a
  obtain ⟨φ, hφ⟩ := powHom_exists A a
  obtain ⟨w, hw⟩ := root_exists A a A.pi
  have hwn : w ∈ nonZeroDivisors A.A := by
    have h1 : w ^ (l ^ a - 1) * w ∈ nonZeroDivisors A.A := by
      rw [← pow_succ, Nat.sub_add_cancel hq, hw]
      exact A.tf
    exact (mul_mem_nonZeroDivisors.1 h1).2
  have hv : ValLike w := by
    rintro f g ⟨m, hm⟩
    obtain ⟨e, he, h1, h2⟩ := hA.2 f g ⟨m, by
      rw [← hw, ← pow_mul, mul_comm, pow_mul]
      exact Ideal.pow_mem_of_mem _ hm _ hq⟩
    exact ⟨e, he, Ideal.mem_span_singleton.1 h1, Ideal.mem_span_singleton.1 h2⟩
  choose u hu using fun i k => Ideal.Quotient.mk_surjective (c i k)
  choose u' hu' using fun i k => Ideal.Quotient.mk_surjective (c' i k)
  have hdvd : w ^ (N + 1) ^ N ∣ A.pi := by
    rw [← hw]
    exact pow_dvd_pow w hN
  have hle : Ideal.span {A.pi} ≤ Ideal.span {w ^ (N + 1) ^ N} :=
    Ideal.span_singleton_le_span_singleton.2 hdvd
  have hsn : SameNorm (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u))
      (redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map u')) := by
    have h2 := (snBasic_of (Qb A) ι).1 (A.A ⧸ Ideal.span {w ^ (N + 1) ^ N}) (Ideal.Quotient.factor hle) _ _ h
    have e1 : ∀ {J : Type} [Fintype J] (v : J → ι → A.A) (d : J → ι → Qb A),
        (∀ i k, Ideal.Quotient.mk _ (v i k) = d i k) →
        (Finset.univ.val.map d).map (fun x k => Ideal.Quotient.factor hle (x k)) =
          redMod (w ^ (N + 1) ^ N) (Finset.univ.val.map v) := by
      intro J _ v d hd
      rw [redMod, Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      funext k
      simp only [Function.comp_apply, ← hd i k]
      exact Ideal.Quotient.factor_mk hle _
    rw [← e1 u c hu, ← e1 u' c' hu']
    exact h2
  have MV : MatchingVal := matchVal_of idemCover_of valLocal_of
    (matchPart_of snBasic_of (matching_of snBasic_of (matchStep_of gaussLin_of snBasic_of linFactor_of)) permMap_of)
  obtain ⟨e, hce, he⟩ := MV A.A w hwn hv ι I I' N hI hI' u u' hsn
  refine ⟨e, hce, fun σ i k => ?_⟩
  obtain ⟨t, ht⟩ := he σ i k
  have hid : e σ ^ l ^ a = e σ := by
    have := (hce.idem σ).pow_succ_eq (l ^ a - 1)
    rwa [Nat.sub_add_cancel hq] at this
  have key : e σ * (u i k ^ l ^ a - u' (σ i) k ^ l ^ a) = A.pi * t ^ l ^ a := by
    have h3 := congrArg φ ht
    rw [map_mul, map_sub, map_mul, hφ, hφ, hφ, hφ, hφ, hid, hw] at h3
    exact h3
  rw [← hu i k, ← hu' (σ i) k, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
  refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨t ^ l ^ a, ?_⟩)
  rw [← mul_sub, key]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.EtaleIdempotents.ExistsOrthogonalIdempotentsSubordinateOfEtaleSec
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.crystallineComparison

private lemma key {R : Type} [CommRing R]
    (hsec : ∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f →
      ∃ s, s ≫ f = 𝟙 _)
    {I : Type} [Finite I] (f : I → R) (hcov : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal) :
    ∃ r : (Π k, Localization.Away (f k)) →+* R,
      r.comp (algebraMap R (Π k, Localization.Away (f k))) = RingHom.id R := by
  let A : I → CommRingCat.{0} := fun k => CommRingCat.of (Localization.Away (f k))
  let m : ∀ k, Spec (A k) ⟶ Spec (CommRingCat.of R) :=
    fun k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))
  let g : ∐ (fun k => Spec (A k)) ⟶ Spec (CommRingCat.of R) := Sigma.desc m
  have hEt : Etale g := by
    refine (IsZariskiLocalAtSource.sigmaDesc (P := @Etale) ?_)
    intro k
    infer_instance
  have hSu : Surjective g := by
    refine ⟨fun p => ?_⟩
    obtain ⟨k, hk⟩ := hcov p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f k)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f k)) (f k)]
      exact hk
    obtain ⟨q, rfl⟩ := hp
    refine ⟨(Sigma.ι (fun k => Spec (A k)) k) q, ?_⟩
    have : Sigma.ι (fun k => Spec (A k)) k ≫ g = m k := Sigma.ι_desc _ _
    rw [← Scheme.Hom.comp_apply, this]
    rfl
  obtain ⟨s, hs⟩ := hsec _ g hEt hSu
  have hg : g = sigmaSpec A ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k)))) := by
    refine Sigma.hom_ext _ _ fun k => ?_
    rw [Sigma.ι_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  let r' := Spec.preimage (s ≫ sigmaSpec A)
  have hr' : Spec.map r' = s ≫ sigmaSpec A := Spec.map_preimage _
  have hc : CommRingCat.ofHom (algebraMap R (Π k, Localization.Away (f k))) ≫ r' = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hr', Category.assoc, ← hg, hs, Spec.map_id]
  exact ⟨r'.hom, congrArg CommRingCat.Hom.hom hc⟩

theorem UpperTheory.exists_orthogonalIdempotents_subordinate_of_etale_sections :
    ∀ (R : Type) [CommRing R],
        (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
        ∀ (ι : Type) (W : ι → Set (PrimeSpectrum R)), (∀ i, IsOpen (W i)) → (∀ p, ∃ i, p ∈ W i) →
        ∃ (I : Type) (_ : Fintype I) (e : I → R) (a : I → ι), CompleteOrthogonalIdempotents e ∧
          ∀ i (p : PrimeSpectrum R), e i ∉ p.asIdeal → p ∈ W (a i) := by
  intro R _ hsec ι W hWo hWc
  classical
  let J : Type := {x : ι × R // (PrimeSpectrum.basicOpen x.2 : Set (PrimeSpectrum R)) ⊆ W x.1}
  have hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ j : J, (PrimeSpectrum.basicOpen j.1.2 : Set (PrimeSpectrum R)) := by
    intro p _
    obtain ⟨i, hi⟩ := hWc p
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi (hWo i)
    exact Set.mem_iUnion.2 ⟨⟨(i, f), hsub⟩, hpf⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun j : J => (PrimeSpectrum.basicOpen j.1.2).isOpen) hcov
  let f : t → R := fun k => k.1.1.2
  have hcovI : ∀ p : PrimeSpectrum R, ∃ k, f k ∉ p.asIdeal := by
    intro p
    obtain ⟨j, hj, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
    exact ⟨⟨j, hj⟩, hp⟩
  obtain ⟨r, hr⟩ := key hsec f hcovI
  have hrf : ∀ x, r (algebraMap R _ x) = x := fun x => congrArg (fun h => h x) hr
  refine ⟨t, inferInstance, fun k => r (Pi.single k 1), fun k => k.1.1.1, ?_, ?_⟩
  · exact (CompleteOrthogonalIdempotents.single (fun k => Localization.Away (f k))).map r
  · intro k p hp
    refine k.1.2 ?_
    show f k ∉ p.asIdeal
    intro hf
    apply hp
    have hu : Pi.single k 1 = algebraMap R (Π k, Localization.Away (f k)) (f k) *
        Pi.single k (IsLocalization.Away.invSelf (f k)) := by
      ext l
      by_cases h : l = k
      · subst h
        simp [IsLocalization.Away.mul_invSelf]
      · simp [Pi.single_eq_of_ne h]
    show r (Pi.single k 1) ∈ p.asIdeal
    rw [hu, map_mul, hrf]
    exact p.asIdeal.mul_mem_right _ hf
end

