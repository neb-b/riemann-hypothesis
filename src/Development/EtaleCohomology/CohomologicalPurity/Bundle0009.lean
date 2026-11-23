module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurPf

def actH (q : ℕ) {P : Arrow Spc} (n : ℤ) {m i j : ℤ} (b : Hs q P m j) :
    Ht q P.right n i →+ Hs q P (n + m) (i + j) where
  toFun a := Hs.act q a b
  map_zero' := by
    apply Subtype.ext
    simp [Hs.act, Hs.proj]
  map_add' x y := by
    apply Subtype.ext
    simp only [Hs.act, Hs.proj, map_add (f := _), AddMonoidHom.add_apply, AddSubgroup.coe_add]
    abel

theorem bij_comp {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] {f : B →+ C} {g : A →+ B}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f.comp g) := by
  rw [AddMonoidHom.coe_comp]; exact hf.comp hg

def purT {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) (P : SP d) (n i : ℤ) :
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d) := by
  classical
  exact if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
    haveI : NeZero q := ⟨h.1⟩
    ((AddEquiv.ofBijective _ (((T P).ok q h.2).2.2.1 (n + 2 * d) (i + d))).symm.toAddMonoidHom.comp
      (actH q (P := abv P.U (T P).π) n (i := i) (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)))).comp
      ((AddEquiv.ofBijective _ (((T P).ok q h.2).1 i n)).symm.toAddMonoidHom.comp
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n))
  else 0

theorem purT_bij {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) : Function.Bijective (purT T q P n i) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dite_eq_left h]
  refine bij_comp (bij_comp (AddEquiv.bijective _) ?_) (bij_comp (AddEquiv.bijective _) (((T P).ok q hq).2.1 i n))
  exact ((T P).ok q hq).2.2.2 n i

def TubeRef {d : ℕ} (T : ∀ P : SP d, Tube P) : Prop := ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

end PurPf

open PurPf

def EtalePurityNaturality : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P), TubeRef T →
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purT T q P n i a) = purT T q P' n i (pull _ (sch.map φ.g) _ _ a)

def EtalePurityProjection : Prop := Hyp → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (purT T q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)

def EtalePurityReduction : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (purT T r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (purT T q P n i a).1

theorem EtalePurity_of_parts (hCl : LeafCl) (hTube : LeafTube) (hN : EtalePurityNaturality) (hP : EtalePurityProjection) (hR : EtalePurityReduction) :
    LeafPur := by
  intro hH d
  obtain ⟨T, hT⟩ := hTube hH d
  exact ⟨purT T, fun q _ P hq =>
    ⟨purT_bij T q P hq, hN hH hCl d T hT q P hq, hP hH d T q P hq, hR hH hCl d T q P hq⟩⟩

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafRankPf

theorem finrank_tensor_surj {A B K X : Type*} [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [Algebra B K] [IsScalarTower A B K] [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (h : Function.Surjective (algebraMap A B)) :
    Module.finrank K (K ⊗[A] X) = Module.finrank K (K ⊗[B] X) := by
  have : CompatibleSMul A B K X := CompatibleSMul.of_algebraMap_surjective K X h
  exact (LinearEquiv.finrank_eq (equivOfCompatibleSMul A B K K X)).symm

theorem finrank_tensor_cotangent {A K : Type*} [CommRing A] [Field K] [Algebra A K] (J : Ideal A)
    (hJ : ∀ a ∈ J, algebraMap A K a = 0) :
    Module.finrank K (K ⊗[A] J) = Module.finrank K (K ⊗[A] J.Cotangent) := by
  have hex := lTensor_exact K (LinearMap.exact_subtype_mkQ (J • (⊤ : Submodule A J)))
    (Submodule.mkQ_surjective _)
  have hz : ∀ (x : K) (z : J), z ∈ J • (⊤ : Submodule A J) → (x ⊗ₜ[A] z : K ⊗[A] J) = 0 := by
    intro x z hz
    refine Submodule.smul_induction_on (p := fun z => (x ⊗ₜ[A] z : K ⊗[A] J) = 0) hz ?_ ?_
    · intro a ha m _
      rw [← smul_tmul, Algebra.smul_def, hJ a ha, zero_mul, zero_tmul]
    · intro u v hu hv
      rw [tmul_add, hu, hv, add_zero]
  have h0 : LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype = 0 := by
    ext x z; exact hz x z z.2
  have hinj : Function.Injective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have : y ∈ LinearMap.range (LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype) :=
      (hex y).mp (by rw [LinearMap.baseChange_eq_ltensor] at hy; exact hy)
    rw [h0, LinearMap.range_zero] at this
    simpa using this
  have hsurj : Function.Surjective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  intro e d R A _ _ _ I p _ hIp hA hB
  have hk : ∀ a ∈ I, algebraMap A p.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hIp ha)
  letI : Algebra (A ⧸ I) p.ResidueField := (Ideal.Quotient.lift I (algebraMap A p.ResidueField) hk).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) p.ResidueField := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹_›) hIp)
  haveI : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  haveI : Algebra.IsStandardSmooth R A := hA.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := hB.isStandardSmooth
  have rA : Module.finrank A Ω[A⁄R] = e + d := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (e + d))
  have rB : Module.finrank (A ⧸ I) Ω[(A ⧸ I)⁄R] = e := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential e)
  have eqv := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) p.ResidueField p.ResidueField Ω[A⁄R]
  have h1 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) = e + d := by
    rw [finrank_tensor_surj hsurj, LinearEquiv.finrank_eq eqv, Module.finrank_baseChange, rA]
  have h2 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[(A ⧸ I)⁄R]) = e := by
    rw [finrank_tensor_surj hsurj, Module.finrank_baseChange, rB]
  have hK : RingHom.ker (algebraMap A (A ⧸ I)) = I := Ideal.mk_ker
  have h3 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] (RingHom.ker (algebraMap A (A ⧸ I))).Cotangent) := by
    rw [← finrank_tensor_cotangent _ (by rw [hK]; exact hk), hK]
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := A ⧸ I) hsurj).mp inferInstance
  have e0 : Function.Exact (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I))
      ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I) hsurj
  have s0 : Function.Surjective ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.mapBaseChange_surjective R A (A ⧸ I) hsurj
  set f := (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I)).baseChange p.ResidueField
  set g := ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A).baseChange p.ResidueField
  have hex : Function.Exact f g := by
    simpa only [f, g, LinearMap.baseChange_eq_ltensor] using lTensor_exact p.ResidueField e0 s0
  have hg : Function.Surjective g := by
    simpa only [g, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective p.ResidueField s0
  have hf : Function.Injective f := by
    have hc : (l.baseChange p.ResidueField).comp f = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := l.baseChange p.ResidueField) (fun x => by
      simpa using LinearMap.congr_fun hc x)
  have : CompatibleSMul A (A ⧸ I) p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R]) :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  haveI : Module.Finite p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) :=
    Module.Finite.equiv ((LinearEquiv.restrictScalars p.ResidueField
      (equivOfCompatibleSMul A (A ⧸ I) p.ResidueField p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R])).symm).trans
      eqv).symm
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf,
    h1, h2] at hrk
  rw [h3]; omega

end LateralTheory.CohomologicalPurity.LeafRankPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSecPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSecPf

theorem LeafSec_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  intro A T _ _ φ I μ hφ hμ
  algebraize [φ]
  have : Algebra.Etale A T := RingHom.etale_algebraMap.mp hφ
  set J : Ideal T := I.map φ with hJ
  have hle : I ≤ J.comap φ := Ideal.le_comap_map
  have hker : ∀ a ∈ J, μ a = 0 := by
    intro a ha
    have : J ≤ RingHom.ker μ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro c hc
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, hμ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    exact this ha
  let q : A ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hle
  let μb : T ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J μ hker
  have hμq : ∀ z, μb (q z) = z := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    show μb (Ideal.Quotient.mk J (φ c)) = _
    simp only [μb, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply, hμ]
  let g : T →ₐ[A] T ⧸ J :=
    { (q.comp μ) with
      commutes' := fun a => by
        show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)
        rw [← RingHom.comp_apply μ φ, hμ]; rfl }
  let f : T →ₐ[A] T ⧸ J := Ideal.Quotient.mkₐ A J
  let ψ : T ⊗[A] T →ₐ[A] T ⧸ J := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]
      congr 1
      all_goals first | rfl | exact hμq _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))
  refine ⟨t, ?_, ?_⟩
  · have h1 : μb (Ideal.Quotient.mk J t) = μ t := Ideal.Quotient.lift_mk _ _ _
    rw [← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]
  · intro s hs
    have h2 := congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2
    have hg : g s = 0 := by show q (μ s) = 0; rw [hs, map_zero]
    rw [hg, zero_mul] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]
    exact h2.symm

end LateralTheory.CohomologicalPurity.LeafSecPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf
section
noncomputable section

namespace LateralTheory.CohomologicalPurity.ChartCut


open RingHom in
theorem shrink_away {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (u v : S)
    (T : Type) [CommRing T] [Algebra S T] [IsLocalization.Away (u * v) T]
    (h : ((algebraMap S (Localization.Away u)).comp ψ).IsStandardSmoothOfRelativeDimension n) :
    ((algebraMap S T).comp ψ).IsStandardSmoothOfRelativeDimension n := by
  let B := Localization.Away (algebraMap S (Localization.Away u) v)
  have h2 : ((algebraMap (Localization.Away u) B).comp
      ((algebraMap S (Localization.Away u)).comp ψ)).IsStandardSmoothOfRelativeDimension n :=
    zero_add n ▸ (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (algebraMap S (Localization.Away u) v)).comp h
  have hB : IsLocalization.Away (u * v) B := inferInstance
  let eT : B ≃ₐ[S] T := IsLocalization.algEquiv (Submonoid.powers (u * v)) B T
  have h3 : ((algebraMap S B).comp ψ).IsStandardSmoothOfRelativeDimension n := by
    rw [IsScalarTower.algebraMap_eq S (Localization.Away u) B, RingHom.comp_assoc]; exact h2
  have h4 := (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left _ eT.toRingEquiv h3
  have hT : algebraMap S T = (eT.toRingEquiv.toRingHom).comp (algebraMap S B) := by
    ext x; exact (eT.commutes x).symm
  rw [hT, RingHom.comp_assoc]; exact h4

theorem LeafShrink_of : LeafShrink := by
  intro e d R A _ _ φ I p hp hIp ⟨h1, h2⟩
  obtain ⟨a, ha1, hap⟩ : ∃ a : A, ((algebraMap A (Localization.Away a)).comp φ).IsStandardSmoothOfRelativeDimension (e + d) ∧ a ∉ p := by
    by_contra hcon
    push Not at hcon
    apply hp.ne_top
    rw [eq_top_iff, ← h1.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  have hq : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  obtain ⟨c, hc1, hcq⟩ : ∃ c : A ⧸ I, ((algebraMap (A ⧸ I) (Localization.Away c)).comp ((Ideal.Quotient.mk I).comp φ)).IsStandardSmoothOfRelativeDimension e ∧ c ∉ p.map (Ideal.Quotient.mk I) := by
    by_contra hcon
    push Not at hcon
    apply hq.ne_top
    rw [eq_top_iff, ← h2.span_eq_top, Ideal.span_le]
    intro g hg; exact hcon g hg
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hbp : b ∉ p := fun hb => hcq (Ideal.mem_map_of_mem _ hb)
  refine ⟨a * b, fun h => (hp.mem_or_mem h).elim hap hbp, ?_⟩
  intro A' _ _ _
  refine ⟨shrink_away φ a b A' ha1, ?_⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)))
      (A' ⧸ I.map (algebraMap A A')) := inferInstance
  have key : Algebra.algebraMapSubmonoid (A ⧸ I) (Submonoid.powers (a * b)) =
      Submonoid.powers (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, mul_comm a b, map_mul]; rfl
  have : IsLocalization.Away (Ideal.Quotient.mk I b * Ideal.Quotient.mk I a)
      (A' ⧸ I.map (algebraMap A A')) := by
    unfold IsLocalization.Away; rw [← key]; exact hloc
  have hcomp : (Ideal.Quotient.mk (I.map (algebraMap A A'))).comp ((algebraMap A A').comp φ) =
      (algebraMap (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))).comp ((Ideal.Quotient.mk I).comp φ) := by
    ext x; rfl
  rw [hcomp]
  exact shrink_away _ _ (Ideal.Quotient.mk I a) _ hc1

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSpanPf

theorem span_of_subsingleton {R P B ι : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R P]
    [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Subsingleton Ω[B⁄P]] (z : ι → P)
    (hz : Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i))) = ⊤ := by
  set T := Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i)))
  have hmap : ∀ m : Ω[P⁄R], KaehlerDifferential.map R R P B m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) := by
      rw [hz]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
    | smul c m _ hm =>
      rw [LinearMap.map_smul, ← algebraMap_smul B c]
      exact T.smul_mem _ hm
  rw [eq_top_iff]
  intro ω _
  have hk : ω ∈ LinearMap.ker (KaehlerDifferential.map R P B B) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hbc : ∀ t, KaehlerDifferential.mapBaseChange R P B t ∈ T := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      exact T.smul_mem _ (hmap m)
    | add a b ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R P B (ω)).mp hk
  exact hbc t

theorem annih {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submodule A M) (p : Ideal A) (hp : p.IsPrime) (f : A) (hf : f ∉ p)
    (h : ∀ ω : M, f • ω ∈ S ⊔ p • ⊤) : ∃ g : A, g ∉ p ∧ ∀ ω : M, g • ω ∈ S := by
  let φ : Module.End A (M ⧸ S) := algebraMap A (Module.End A (M ⧸ S)) f
  have hφ : LinearMap.range φ ≤ p • ⊤ := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨ω, rfl⟩ := S.mkQ_surjective n
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (h ω)
    have e1 : φ (S.mkQ ω) = S.mkQ t := by
      simp only [φ, Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, ← hst,
        Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero S).mpr hs, zero_add]
    rw [e1]
    exact (Submodule.smul_mono (le_refl p) (le_top : Submodule.map S.mkQ ⊤ ≤ ⊤)) (by rw [← Submodule.map_smul'']; exact Submodule.mem_map_of_mem ht)
  obtain ⟨q, hmon, -, hcoef, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero _ φ p hφ
  refine ⟨Polynomial.aeval f q, ?_, ?_⟩
  · intro hmem
    apply hf
    apply hp.mem_of_pow_mem q.natDegree
    have hsum : Polynomial.aeval f q = f ^ q.natDegree + ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree]
      simp [add_comm, smul_eq_mul]
    have hlow : ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k ∈ p :=
      Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _
        (Ideal.pow_le_self (by have := Finset.mem_range.mp hk; omega) (hcoef k))
    have := p.sub_mem hmem hlow
    rwa [hsum, add_sub_cancel_right] at this
  · intro ω
    have e2 : Polynomial.aeval φ q = algebraMap A (Module.End A (M ⧸ S)) (Polynomial.aeval f q) :=
      Polynomial.aeval_algebraMap_apply _ _ _
    have := LinearMap.congr_fun hq (S.mkQ ω)
    rw [e2, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this


open KaehlerDifferential in
theorem key {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {e d : ℕ}
    (x : Fin d → A) (y : Fin e → A) (f : A) (hx : ∀ j, x j ∈ I)
    (hfI : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x))
    (hspan : Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤)
    (ω : Ω[A⁄R]) :
    f • ω ∈ Submodule.span A (Set.range fun k => D R A (Sum.elim x y k)) ⊔ I • ⊤ := by
  set S := Submodule.span A (Set.range fun k => D R A (Sum.elim x y k))
  have hSx : ∀ j, D R A (x j) ∈ S := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hSy : ∀ k, D R A (y k) ∈ S := fun k => Submodule.subset_span ⟨Sum.inr k, rfl⟩
  have hI : ∀ a ∈ I, ∀ m : Ω[A⁄R], a • m ∈ S ⊔ I • ⊤ := fun a ha m =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ha trivial)
  have hDa : ∀ a ∈ I, f • D R A a ∈ S ⊔ I • ⊤ := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hfI a ha)
    have e1 : D R A (f * a) = f • D R A a + a • D R A f := Derivation.leibniz _ _ _
    have e2 : D R A (f * a) = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb, map_sum]; simp only [Derivation.leibniz]
    have e3 : f • D R A a = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) - a • D R A f := by
      rw [← e2, e1]; abel
    rw [e3]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_) (hI a ha _)
    · exact Submodule.mem_sup_left (S.smul_mem _ (hSx j))
    · exact hI _ (hx j) _
  have hω : map R R A (A ⧸ I) ω ∈
      Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hω
  choose c' hc' using fun k => Ideal.Quotient.mk_surjective (c k)
  set ω' := ω - ∑ k, c' k • D R A (y k) with hω'
  have hck : ∀ k, c' k • D R (A ⧸ I) (algebraMap A (A ⧸ I) (y k)) =
      c k • D R (A ⧸ I) (Ideal.Quotient.mk I (y k)) := by
    intro k
    rw [← algebraMap_smul (A ⧸ I) (c' k), Ideal.Quotient.algebraMap_eq, hc']
  have h0 : mapBaseChange R A (A ⧸ I) (1 ⊗ₜ ω') = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mapBaseChange_tmul, one_smul, hω', map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, map_D, hck, hc, sub_self]
  obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I)
    Ideal.Quotient.mk_surjective (1 ⊗ₜ ω')).mp h0
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [kerCotangentToTensor_toCotangent] at ht
  have haI : (a : A) ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp a.2
  have hdiff : ω' - D R A a ∈ I • (⊤ : Submodule A Ω[A⁄R]) := by
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] (ω' - D R A a) = 0 := by rw [tmul_sub, ← ht, sub_self]
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[A⁄R] I) h1
    rwa [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
  have e4 : f • ω = f • (ω' - D R A a) + f • ∑ k, c' k • D R A (y k) + f • D R A a := by
    rw [← smul_add, ← smul_add, hω']; congr 1; abel
  rw [e4]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (hDa a haI)
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ f hdiff)
  · exact Submodule.mem_sup_left (S.smul_mem _ (Submodule.sum_mem _ fun k _ => S.smul_mem _ (hSy k)))

theorem LeafSpan_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  intro e d R A _ _ _ _ I p hp hIp hB x f hx hf hfI
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := e) R (A ⧸ I)
  choose y hy using fun k : Fin e => Ideal.Quotient.mk_surjective (g (MvPolynomial.X k))
  have hspan : Submodule.span (A ⧸ I)
      (Set.range fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤ := by
    let _ : Algebra (MvPolynomial (Fin e) R) (A ⧸ I) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin e) R) (A ⧸ I) := hg
    have : IsScalarTower R (MvPolynomial (Fin e) R) (A ⧸ I) :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    have h := span_of_subsingleton (R := R) (P := MvPolynomial (Fin e) R) (B := A ⧸ I)
      MvPolynomial.X (by
        rw [← (KaehlerDifferential.mvPolynomialBasis R (Fin e)).span_eq]
        congr 2; funext i; simp [KaehlerDifferential.mvPolynomialBasis_apply])
    have e5 : (fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) =
        fun k => KaehlerDifferential.D R (A ⧸ I)
          (algebraMap (MvPolynomial (Fin e) R) (A ⧸ I) (MvPolynomial.X k)) := by
      funext k; rw [hy]; rfl
    rw [e5]; exact h
  obtain ⟨g', hg'p, hg'⟩ := annih
    (Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))) p hp f hf
    (fun ω => (show _ ⊔ I • (⊤ : Submodule A Ω[A⁄R]) ≤ _ ⊔ p • ⊤ from
      sup_le_sup_left (Submodule.smul_mono_left hIp) _) (key I x y f hx hfI hspan ω))
  exact ⟨y, g', hg'p, hg'⟩

end LateralTheory.CohomologicalPurity.LeafSpanPf
end
end

