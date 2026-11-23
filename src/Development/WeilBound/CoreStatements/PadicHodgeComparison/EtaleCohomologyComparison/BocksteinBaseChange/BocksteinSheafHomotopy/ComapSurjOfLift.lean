module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial

namespace CrystallineSemistableComparison.KummerTwistLemmas

open GlobalTheory.EtC

theorem comap_surj_of_lift {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : A →+* K), ∃ χ : S →+* K, χ.comp (algebraMap A S) = ψ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A S)) := by
  intro p
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let ψ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  obtain ⟨χ, hχ⟩ := h K ψ
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change χ (algebraMap A S a) = 0 ↔ a ∈ p.asIdeal
  rw [← RingHom.comp_apply, hχ]
  simp only [ψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField K).injective]
  rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

theorem etaleCover (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S))) :
    ∃ (W : Scheme.{0}) (π : W ⟶ U) (φ : S →+* Γ(W, ⊤)),
      Sieve.ofArrows (fun _ : Unit => W) (fun _ => π) ∈ Scheme.etaleTopology U ∧
      ∀ a, φ (algebraMap Γ(U, ⊤) S a) = π.appTop.hom a := by
  let φ0 : Γ(U, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)
  have : Etale (Spec.map φ0) := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map φ0) := ⟨hS⟩
  have : Surjective (pullback.fst U.toSpecΓ (Spec.map φ0)) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
  refine ⟨pullback U.toSpecΓ (Spec.map φ0), pullback.fst _ _,
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop).hom, ?_, ?_⟩
  · let 𝒰 : U.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Unit
      (fun _ => pullback U.toSpecΓ (Spec.map φ0)) (fun _ => pullback.fst _ _)
      (fun x => ⟨(), (pullback.fst U.toSpecΓ (Spec.map φ0)).surjective x⟩) (fun _ => inferInstance)
    exact 𝒰.mem_grothendieckTopology
  · intro a
    have h := congrArg Scheme.Hom.appTop (pullback.condition (f := U.toSpecΓ) (g := Spec.map φ0))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
    have key : φ0 ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd U.toSpecΓ (Spec.map φ0)).appTop =
        (pullback.fst U.toSpecΓ (Spec.map φ0)).appTop := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(U, ⊤)).hom, h, ← Category.assoc, ← Scheme.ΓSpecIso_naturality]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun k => k.hom a) key

theorem loc_of_etale (U : Scheme.{0}) (S : Type) [CommRing S] [Algebra Γ(U, ⊤) S] [Algebra.Etale Γ(U, ⊤) S]
    (hS : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(U, ⊤) S)))
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (χ : S →+* Γ(V, ⊤)), (∀ a, χ (algebraMap Γ(U, ⊤) S a) = g.appTop.hom a) → P V g) :
    Loc U P := by
  obtain ⟨W, π, φ, hmem, hφ⟩ := etaleCover U S hS
  refine ⟨_, hmem, fun V g hg => ?_⟩
  obtain ⟨_, h, _, ⟨i⟩, rfl⟩ := hg
  refine hP V (h ≫ π) (h.appTop.hom.comp φ) fun a => ?_
  rw [RingHom.comp_apply, hφ, Scheme.Hom.comp_appTop]
  rfl

theorem kumLoc (U : Scheme.{0}) (m : ℕ) (u : (Γ(U, ⊤))ˣ) (hm : IsUnit (m : Γ(U, ⊤))) :
    Loc U fun V g => ∃ v : Γ(V, ⊤), v ^ m = g.appTop.hom u.1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨1, ?_⟩⟩
    have h01 : (0 : Γ(U, ⊤)) = 1 := by simpa using isUnit_zero_iff.mp (by simpa using hm)
    have h01' : (0 : Γ(V, ⊤)) = 1 := by simpa using congrArg g.appTop.hom h01
    have := subsingleton_of_zero_eq_one h01'
    exact Subsingleton.elim _ _
  · let c : Γ(U, ⊤) := (hm.unit⁻¹ : (Γ(U, ⊤))ˣ)
    have hc : c * (m : Γ(U, ⊤)) = 1 := hm.val_inv_mul
    let Pp : StandardEtalePair Γ(U, ⊤) :=
      { f := X ^ m - C u.1
        monic_f := monic_X_pow_sub_C _ hm0.ne'
        g := X
        cond := ⟨C c * X, 0, m, by
          rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
          have hX : (X : (Γ(U, ⊤))[X]) ^ (m - 1) * X = X ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
          have hC : C (m : Γ(U, ⊤)) * C c = 1 := by rw [← C_mul, mul_comm, hc, C_1]
          linear_combination (X ^ (m - 1) * X) * hC + hX⟩ }
    refine loc_of_etale U Pp.Ring (comap_surj_of_lift fun K _ _ ψ => ?_) _ fun V g χ hχ => ?_
    · obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ψ u.1) hm0
      let _ := ψ.toAlgebra
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_pow hm0.ne'] at hx
        exact (u.isUnit.map ψ).ne_zero hx.symm
      have hmap : Pp.HasMap x := ⟨by simp [Pp, hx, RingHom.algebraMap_toAlgebra], by simpa [Pp] using hx0⟩
      exact ⟨(Pp.lift x hmap).toRingHom, (Pp.lift x hmap).comp_algebraMap⟩
    · refine ⟨χ Pp.X, ?_⟩
      have h0 := (StandardEtalePair.hasMap_X (P := Pp)).1
      have h1 : Pp.X ^ m = algebraMap Γ(U, ⊤) Pp.Ring u.1 := by
        simpa [Pp, sub_eq_zero] using h0
      rw [← map_pow, h1, hχ]

end CrystallineSemistableComparison.KummerTwistLemmas
