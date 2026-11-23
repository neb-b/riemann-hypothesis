module

public import Development.EtaleCohomology.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepPf
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def SHInsepLoc : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → IsLocalRing (A ⊗[κ] K)

def SHInsepHens : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], HenselianLocalRing (A ⊗[κ] K)

def SHInsepRes : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A], SH A → ∀ [IsLocalRing (A ⊗[κ] K)], IsSepClosed (IsLocalRing.ResidueField (A ⊗[κ] K))

theorem SHInsep_of (hL : SHInsepLoc) (hH : SHInsepHens) (hR : SHInsepRes) : SHInsep := by
  intro κ K A _ _ _ _ _ _ hA
  have := hL κ K A hA
  exact ⟨hH κ K A hA, hR κ K A hA⟩

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHInvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem shinv_eqv_of_iso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem shinv_pull_comp_fun {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R) (n : ℤ) :
    (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
  funext x; exact pull_comp R f g F n x

theorem shinv_eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n; rw [shinv_pull_comp_fun]; exact (hf n).comp (hg n)

theorem shinv_eqv_right {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) : Eqv R g F := by
  intro n; have := hfg n; rw [shinv_pull_comp_fun] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

theorem SHInv_of (hAlgExt : AlgExt) (hInsep : Insep) : SHInv := by
  intro hA9 hB2 hB3 hE2 hE3 q _ k _ _ hq X p _ _ A s hSH i
  obtain ⟨hHL, hsc⟩ := hSH
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  have hqκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hqA.map (IsLocalRing.residue A)
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure _ _).mp hsc
  let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let alg := Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A)
    (AlgebraicClosure (IsLocalRing.ResidueField A))))
  let pA := pullback.snd p (Spec.map s)
  have h1 : Eqv _ (sch.map (pullback.fst pA res)) (tw q i) := hE2 q A ⟨hHL, hsc⟩ hqA pA i
  have h2 : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg)) (tw q i) :=
    hInsep hA9 hB2 hB3 q _ _ hqκ (pullback.snd pA res) i
  let f : k →+* AlgebraicClosure (IsLocalRing.ResidueField A) :=
    (algebraMap (IsLocalRing.ResidueField A) _).comp ((IsLocalRing.residue A).comp s.hom)
  have h3 := hAlgExt hE2 hE3 q k _ f hq p i
  have hf : Spec.map (CommRingCat.ofHom f) = (alg ≫ res) ≫ Spec.map s := by
    simp only [alg, res, ← Spec.map_comp]; rfl
  have h3' : Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
    have key : ∀ g, g = (alg ≫ res) ≫ Spec.map s → Eqv _ (sch.map (pullback.fst p g)) (tw q i) →
        Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
      intro g hg h; subst hg; exact h
    exact key _ hf h3
  have hcomp : pullback.fst (pullback.snd pA res) alg ≫ pullback.fst pA res ≫ pullback.fst p (Spec.map s) =
      ((pullbackLeftPullbackSndIso pA res alg).hom ≫ (pullbackLeftPullbackSndIso p (Spec.map s) (alg ≫ res)).hom) ≫
        pullback.fst p ((alg ≫ res) ≫ Spec.map s) := by
    rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst p (Spec.map s) (alg ≫ res)]
    erw [← Category.assoc (pullbackLeftPullbackSndIso pA res alg).hom, pullbackLeftPullbackSndIso_hom_fst pA res alg]
    rw [Category.assoc]
  have hall : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg) ≫ sch.map (pullback.fst pA res) ≫
      sch.map (pullback.fst p (Spec.map s))) (tw q i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp, Functor.map_comp]
    exact shinv_eqv_comp (shinv_eqv_of_iso _ _) h3'
  exact shinv_eqv_right h1 (shinv_eqv_right h2 hall)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.TwSecPfGamma
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.TwSecPfGamma

theorem map_symm_map {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) :
    (f.map (e.symm : B →+* A)).map (e : A →+* B) = f := by
  rw [Polynomial.map_map]
  have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
    ext x; simp
  rw [this, Polynomial.map_id]

theorem mem_max_iff {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (x : B) :
    e.symm x ∈ IsLocalRing.maximalIdeal A ↔ x ∈ IsLocalRing.maximalIdeal B := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [isUnit_map_iff e.symm x]

theorem henselian_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) [hA : HenselianLocalRing A] :
    HenselianLocalRing B := by
  haveI : Nontrivial A := inferInstance
  haveI : Nontrivial B := e.injective.nontrivial
  haveI : IsLocalRing B := IsLocalRing.of_surjective' (e : A →+* B) e.surjective
  refine { is_henselian := ?_ }
  intro f hf a₀ h1 h2
  have hev : ∀ (p : B[X]) (b : B), (p.map (e.symm : B →+* A)).eval (e.symm b) = e.symm (p.eval b) := by
    intro p b
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom (e.symm : B →+* A) b
  obtain ⟨a, ha, hmem⟩ := hA.is_henselian (f.map (e.symm : B →+* A)) (hf.map _) (e.symm a₀)
    (by rw [hev, mem_max_iff]; exact h1)
    (by rw [Polynomial.derivative_map, hev]; exact (isUnit_map_iff e.symm _).2 h2)
  refine ⟨e a, ?_, ?_⟩
  · have := ha.map (f := (e : A →+* B))
    rwa [map_symm_map] at this
  · rw [← mem_max_iff e]
    have : e.symm (e a - a₀) = a - e.symm a₀ := by simp
    rw [this]; exact hmem

theorem sepClosed_of_equiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : (p.map (e.symm : L →+* K)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro h
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (p.map (e.symm : L →+* K)) hdeg (hsep.map)
  refine ⟨e x, ?_⟩
  have := hx.map (f := (e : K →+* L))
  rw [map_symm_map] at this
  exact this

theorem SH_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : SH A) : SH B := by
  obtain ⟨hA, hs⟩ := h
  haveI := hA
  haveI := henselian_of_equiv e
  refine ⟨inferInstance, ?_⟩
  haveI := hs
  exact sepClosed_of_equiv (IsLocalRing.ResidueField.mapEquiv e)

end LateralTheory.KummerTheory.TwSecPfGamma

namespace LateralTheory.KummerTheory

theorem SHGamma_holds (A : Type) [CommRing A] (h : SH A) : SH Γ(Spec (CommRingCat.of A), ⊤) :=
  TwSecPfGamma.SH_of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm h

end LateralTheory.KummerTheory
end
end

