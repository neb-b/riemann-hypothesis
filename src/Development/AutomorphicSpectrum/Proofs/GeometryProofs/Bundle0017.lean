module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenComponentMapCompat
section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigMap

open GlobalTheory.CompanionTheory.Ar

section Indep

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem mem_eigSp_iff' (ρ : O →+* Module.End k V) (σ : O →+* k) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_sum_eq_zero (ρ : O →+* Module.End k V) (s : Finset (O →+* k)) :
    ∀ f : (O →+* k) → V, (∀ t ∈ s, f t ∈ eigSp ρ t) → ∑ t ∈ s, f t = 0 → ∀ t ∈ s, f t = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t₀ s ht₀ ih =>
    intro f hf hsum
    have hf' : ∀ t ∈ s, f t ∈ eigSp ρ t := fun t ht => hf t (Finset.mem_insert_of_mem ht)
    have hf₀ := (mem_eigSp_iff' ρ t₀ _).1 (hf t₀ (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ht₀] at hsum
    have hs : ∀ t ∈ s, f t = 0 := by
      intro t ht
      have hne : t ≠ t₀ := fun e => ht₀ (e ▸ ht)
      obtain ⟨a, ha⟩ : ∃ a, t a ≠ t₀ a := by
        by_contra hcon
        push Not at hcon
        exact hne (RingHom.ext hcon)
      have hz : ∑ u ∈ s, (u a - t₀ a) • f u = 0 := by
        have h1 : ρ a (f t₀ + ∑ u ∈ s, f u) - t₀ a • (f t₀ + ∑ u ∈ s, f u) = 0 := by
          rw [hsum]; simp
        have h2 : ρ a (∑ u ∈ s, f u) = ∑ u ∈ s, u a • f u := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_congr rfl fun u hu => (mem_eigSp_iff' ρ u _).1 (hf' u hu) a
        rw [map_add (f := _), hf₀ a, h2, smul_add, Finset.smul_sum] at h1
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        abel
      have := ih (fun u => (u a - t₀ a) • f u)
        (fun u hu => Submodule.smul_mem _ _ (hf' u hu)) hz t ht
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
    have h₀ : f t₀ = 0 := by
      rw [Finset.sum_eq_zero hs, add_zero] at hsum
      exact hsum
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact h₀
    · exact hs t ht

theorem iSupIndep_eigSp (ρ : O →+* Module.End k V) : iSupIndep (fun σ : O →+* k => eigSp ρ σ) :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).2 fun s v hv h0 i hi =>
    eigSp_sum_eq_zero ρ s v hv h0 i hi

theorem eq_zero_of_mem_eigSp_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {y : V}
    (h₁ : y ∈ eigSp ρ σ) (h₂ : y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ') : y = 0 :=
  Submodule.disjoint_def.1 (iSupIndep_eigSp ρ σ) y h₁ (by simpa using h₂)

end Indep

theorem eigComp_map {k k' V V' O : Type} [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V') (hj : ∀ (c : k) x, j (c • x) = κ c • j x)
    (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V') (hρ : ∀ a x, ρ' a (j x) = j (ρ a x))
    (σ : O →+* k) (x : V) (hx : eigComp ρ σ x ≠ 0) :
    eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  have hmap : ∀ (s : O →+* k) (y : V), y ∈ eigSp ρ s → j y ∈ eigSp ρ' (κ.comp s) := by
    intro s y hy
    refine (mem_eigSp_iff' ρ' _ _).2 fun a => ?_
    rw [hρ, (mem_eigSp_iff' ρ s y).1 hy a, hj]
    rfl
  have hsup : ∀ y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ',
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y =>
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
    · intro s y hy
      refine Submodule.iSup_induction _ (motive := fun y =>
        j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
      · intro hs y hy
        have hne : κ.comp s ≠ κ.comp σ := fun e => hs (RingHom.ext fun a =>
          κ.injective (RingHom.congr_fun e a))
        exact Submodule.mem_iSup_of_mem (κ.comp s) (Submodule.mem_iSup_of_mem hne (hmap s y hy))
      · intro a b ha hb
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
  have h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ' := by
    by_contra hcon
    exact hx (by rw [eigComp, dite_eq_right hcon])
  have hp : eigComp ρ σ x = h.choose := by rw [eigComp, dite_eq_left h]
  obtain ⟨hp₁, hp₂⟩ := h.choose_spec
  rw [← hp] at hp₁ hp₂
  have hp₃ := hsup _ hp₂
  rw [map_sub] at hp₃
  have h' : ∃ q ∈ eigSp ρ' (κ.comp σ), j x - q ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' :=
    ⟨_, hmap σ _ hp₁, hp₃⟩
  have hq : eigComp ρ' (κ.comp σ) (j x) = h'.choose := by rw [eigComp, dite_eq_left h']
  obtain ⟨hq₁, hq₂⟩ := h'.choose_spec
  rw [← hq] at hq₁ hq₂
  refine sub_eq_zero.1 (eq_zero_of_mem_eigSp_of_mem_iSup ρ' (κ.comp σ)
    (Submodule.sub_mem _ hq₁ (hmap σ _ hp₁)) ?_)
  have : eigComp ρ' (κ.comp σ) (j x) - j (eigComp ρ σ x) =
      (j x - j (eigComp ρ σ x)) - (j x - eigComp ρ' (κ.comp σ) (j x)) := by abel
  rw [this]
  exact Submodule.sub_mem _ hp₃ hq₂

end GlobalTheory.CompanionTheory.Ar.Cusp.EigMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.RegDenom

theorem exists_denom_of_injective {R K B S : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Finite S]
    (ρ : R →+* B) (v : S → B →+* K) (hv : Function.Injective v)
    (hρ : ∀ i r, v i (ρ r) = algebraMap R K r) (f : S → K) :
    ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * f i := by
  classical
  cases nonempty_fintype S
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  let W : Submodule K (S → K) := Submodule.span K (Set.range fun b : B => fun i => v i b)
  have hW : W = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    have hm : Function.Injective (fun i : S => ((v i : B →+* K) : B →* K)) := by
      intro i j hij
      apply hv
      ext b
      exact DFunLike.congr_fun hij b
    have hli : LinearIndependent K (fun i : S => (fun b => v i b : B → K)) :=
      (linearIndependent_monoidHom B K).comp _ hm
    have hc : ∀ i, φ (Pi.single i 1) = 0 := by
      have h0 := Fintype.linearIndependent_iff.mp hli (fun i => φ (Pi.single i 1)) (by
        funext b
        have hb : φ (fun i => v i b) = 0 := hle (Submodule.subset_span ⟨b, rfl⟩)
        have hx : (fun i => v i b) = ∑ i, (v i b) • (Pi.single i (1 : K) : S → K) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hx, map_sum] at hb
        simp only [map_smul, smul_eq_mul] at hb
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hb]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      exact h0
    apply hφ
    ext i
    simpa using hc i

  have key : ∀ x ∈ W, ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * x i := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨b, rfl⟩ := h
      exact ⟨1, one_ne_zero, b, fun i => by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨e, he, c, hc⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ρ e * b + ρ d * c, fun i => ?_⟩
      simp only [map_add (f := _), map_mul, hρ, hb, hc, Pi.add_apply]
      ring
    | smul k x _ hx =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
      have hcK : algebraMap R K c ≠ 0 := fun h => hc0 (inj (by simpa using h))
      refine ⟨c * d, mul_ne_zero hc0 hd, ρ a * b, fun i => ?_⟩
      simp only [map_mul, hρ, hb, Pi.smul_apply, smul_eq_mul]
      field_simp
  exact key f (hW ▸ Submodule.mem_top)

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem eq_of_valHom_eq {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : valHom x U hx = valHom y U hy) : x = y := by
  have ha : x.appLE U ⊤ hx = y.appLE U ⊤ hy := by
    ext s
    have := DFunLike.congr_fun e s
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1 this
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of B)).Opens) := isAffineOpen_top _
  have h1 := hU.SpecMap_appLE_fromSpec x htop hx
  have h2 := hU.SpecMap_appLE_fromSpec y htop hy
  rw [ha, h2] at h1
  have : IsIso htop.fromSpec := by
    rw [show htop = isAffineOpen_top _ from rfl, IsAffineOpen.fromSpec_top]
    infer_instance
  exact (cancel_epi htop.fromSpec).mp h1.symm

theorem le_preimage_top {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

def structHom {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (le_preimage_top p U)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valHom_structHom {B : Type} [CommRing B] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (i : R →+* B) (x : Spec (CommRingCat.of B) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom i))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : valHom x U h (structHom p U r) = i r := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom i := by
    have e1 : p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h = (x ≫ p).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [Scheme.Hom.appLE, Scheme.Hom.comp_appTop, Scheme.Hom.appTop]
      refine Eq.trans (congrArg _ ?_) (Category.comp_id _)
      exact (Spec (CommRingCat.of B)).presheaf.map_id _
    rw [reassoc_of% e1, hx, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congr($(e).hom r)

theorem exists_denom_regularAt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left),
    ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  intro R _ _ T _ _ Γ f g
  obtain ⟨U, hU, hg, -⟩ := exists_isAffineOpen_mem_and_subset (x := g) (U := ⊤) trivial
  let S := {t : T // ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U}
  let v : S → Γ(Γ.G.left, U) →+* FractionRing R := fun t => valHom (Γ.pt t.1).left U t.2
  have hv : Function.Injective v := by
    intro s t e
    have hst := eq_of_valHom_eq hU s.2 t.2 e
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
    exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
  have hρ : ∀ t r, v t (structHom Γ.G.hom U r) = algebraMap R _ r := fun t r =>
    valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t.1)) U t.2 r
  obtain ⟨d, hd, b, hb⟩ := exists_denom_of_injective (structHom Γ.G.hom U) v hv hρ (fun t => f t.1)
  exact ⟨d, hd, U, hg, b, fun t h => hb ⟨t, h⟩⟩

end GlobalTheory.CompanionTheory.Ar.BT.RegDenom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem comp_hom_apply_pointOfLocal {a b c d : CommRingCat.{0}} (A : a ⟶ b) (B : b ⟶ c) (D : a ⟶ c) (T : c ⟶ d)
    (e : A ≫ B = D) (s : a) : (B ≫ T).hom (A.hom s) = (D ≫ T).hom s := by
  subst e
  simp

theorem genMap_apply_of_specializes_pointOfLocal {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes p.2 =
      X.presheaf.stalkSpecializes q.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  unfold genMap
  exact comp_hom_apply_pointOfLocal _ _ _ _ e s

theorem exists_unique_point_of_local (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R)
    (hφ : IsLocalHom φ) :
    ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  let e : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have he : ∀ s, ((e s : regAt ξ p) : Ω) = genMap ξ p s := fun s => rfl
  have einj : Function.Injective e := fun s t h => hξ.inj p (by rw [← he, ← he, h])
  have esurj : Function.Surjective e := (genMap ξ p).rangeRestrict_surjective
  let ψ : X.presheaf.stalk p.1 ⟶ CommRingCat.of R := CommRingCat.ofHom (φ.comp e)
  have hψ : ∀ s, ψ.hom s = φ (e s) := fun s => rfl
  have hloc : IsLocalHom ψ.hom := by
    refine ⟨fun s hs => ?_⟩
    have h1 : IsUnit (e s) := hφ.map_nonunit _ (by rwa [hψ] at hs)
    obtain ⟨b, hb⟩ := h1.exists_right_inv
    obtain ⟨t, rfl⟩ := esurj b
    have : s * t = 1 := einj (by rw [map_mul, hb, map_one])
    exact IsUnit.of_mul_eq_one t this
  let w : Σ x, { f : X.presheaf.stalk x ⟶ CommRingCat.of R // IsLocalHom f.hom } := ⟨p.1, ψ, hloc⟩
  let E := SpecToEquivOfLocalRing X (CommRingCat.of R)
  have key : ∀ y : Spec (CommRingCat.of R) ⟶ X, ∀ hc : centre y = p.1,
      (∀ s : X.presheaf.stalk (centre y),
        (Scheme.stalkClosedPointTo y).hom s =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s)) → y = E.symm w := by
    intro y hc h
    rw [Equiv.eq_symm_apply]
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hc, ?_⟩
    ext s
    exact h s
  refine ⟨E.symm w, ?_, ?_⟩
  · have hs := E.apply_symm_apply w
    obtain ⟨hc, hT⟩ := SpecToEquivOfLocalRing_eq_iff.mp hs
    have hc' : centre (E.symm w) = p.1 := hc
    refine ⟨hc', fun a => ?_⟩
    obtain ⟨s, hsa⟩ := a.2
    have hsa' : e s = a := Subtype.ext hsa
    have hg : genPt ξ ⤳ centre (E.symm w) := hc'.symm ▸ p.2
    refine ⟨hg, (X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s, ?_, ?_⟩
    · exact (genMap_apply_of_specializes_pointOfLocal ξ ⟨_, hg⟩ p (specializes_of_eq hc') s).trans hsa
    · have h1 := congrArg (fun f => f.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) hT
      have h1' : (Scheme.stalkClosedPointTo (E.symm w)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
            ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) := h1
      have h2 : (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) = s := by
        have h3 : X.presheaf.stalkSpecializes (specializes_of_eq hc') ≫
            X.presheaf.stalkSpecializes (specializes_of_eq hc.symm) = 𝟙 _ := by
          rw [TopCat.Presheaf.stalkSpecializes_comp]
          exact TopCat.Presheaf.stalkSpecializes_refl _ _
        have h4 := congrArg (fun f => f.hom s) h3
        exact h4
      rw [h2, hψ, hsa'] at h1'
      exact h1'
  · rintro y ⟨hc, hv⟩
    refine key y hc fun s => ?_
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s := ⟨_, rfl⟩
    obtain ⟨hg, s1, hs1, hr⟩ := hv (e s0)
    have h1 : s1 = s := by
      apply hξ.inj ⟨_, hg⟩
      rw [hs1, he, hs0]
      exact genMap_apply_of_specializes_pointOfLocal ξ p ⟨_, hg⟩ (specializes_of_eq hc.symm) s
    rw [← hs0, hψ, ← hr, h1]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TanLift

theorem comp_one_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact MonObj.comp_one u

theorem comp_mul_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    u ≫ (a * b) = (u ≫ a) * (u ≫ b) := by
  exact MonObj.comp_mul u a b

theorem comp_pow_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a : X ⟶ M) (n : ℕ) :
    u ≫ a ^ n = (u ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_mul_over, ih]

section

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

theorem pt_zero (M : LieModel G x L) : M.pt 0 = 1 := by
  have h : M.pt 0 * M.pt 0 = M.pt 0 := by rw [← M.5, add_zero]
  exact mul_eq_left.mp h

theorem pt_nsmul (M : LieModel G x L) (e : L) (n : ℕ) : M.pt (n • e) = M.pt e ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_zero]
  | succ n ih => rw [succ_nsmul, M.5, ih, pow_succ]

theorem dualMap_epsMul (I : Ideal R) (c : R) (hc : Ideal.Quotient.mk I c = 0) :
    (dualMap (Ideal.Quotient.mk I)).comp (epsMul c) =
      ((algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I)).comp
        (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, hc]

theorem dualMap_algebraMap (I : Ideal R) :
    (dualMap (Ideal.Quotient.mk I)).comp (algebraMap R (DualNumber R)) =
      (algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end

theorem tangent_mod_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L), ∃! (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M e
  obtain ⟨-, -, hinj, htors⟩ := hi
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
      (Ideal.Quotient.mk (Ideal.span {(N : R)})))))
  have hu : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
      (GlobalTheory.CompanionTheory.Ar.epsAt x).hom = (Over.mk (Y.hom ≫ x)).hom := by
    simp only [GlobalTheory.CompanionTheory.Ar.epsAt, Over.mk_hom, Y]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_algebraMap]
  let u : Over.mk (Y.hom ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x := Over.homMk _ hu
  let u₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (N : R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have htan : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left =
      (1 : Over.mk x ⟶ G).left := M.2 e
  have hg : (u ≫ M.pt e) ^ N = 1 := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_pow_over, ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_nsmul, ← Nat.cast_smul_eq_nsmul R,
      ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u₀]
    apply Over.OverMorphism.ext
    have e₁ : (u ≫ M.pt ((N : R) • e)).left =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (N : R))) ≫ (M.pt e).left := by
      rw [Over.comp_left, M.6]
      rfl
    have e₂ : (u₀ ≫ (1 : Over.mk x ⟶ G)).left =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
            (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left := by
      rw [Over.comp_left, htan]
      rfl
    rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_epsMul _ _ hN]
  obtain ⟨y, hy⟩ := (htors Y (u ≫ M.pt e)).1 hg
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · rw [hy]
    rfl
  · rintro v ⟨hv₁, hv₂⟩
    have hv : Over.homMk (U := Y) (V := Γ.G) v hv₁ = y := by
      refine hinj Y _ y ?_
      change v ≫ i = _
      rw [hv₂, hy]
      rfl
    calc v = (Over.homMk (U := Y) (V := Γ.G) v hv₁).left := rfl
      _ = y.left := by rw [hv]

end GlobalTheory.CompanionTheory.Ar.BT.TanLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def Char0 (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Prop := ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p

def Pts (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Subring Ω) :=
  {R | ∃ p : Cpt ξ, Char0 ξ p ∧ R = regAt ξ p}

def IsLocAt [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (q : Ideal A) (R : Subring Ω) : Prop :=
  ∀ a : Ω, a ∈ R ↔ ∃ s : A, s ∉ q ∧ (s : Ω) * a ∈ A

structure IsSncPatch [Algebra ℚ Ω] (Pt Bd : Set (Subring Ω)) (e : ℕ) (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) :
    Prop where
  fg : A.FG
  smooth : Algebra.Smooth ℚ A
  le : n ≤ e
  li : LinearIndependent A fun i => KaehlerDifferential.D ℚ A (z i)
  span : Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤
  pts : ∀ q : Ideal A, q.IsPrime → ∃ R ∈ Pt, IsLocAt A q R ∧ (R ∈ Bd ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

