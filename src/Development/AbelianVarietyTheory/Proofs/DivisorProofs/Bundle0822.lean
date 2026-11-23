module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnifPull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
  {φ : G'.left ⟶ G.left}

def push (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : Over.mk t ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, hw, ← Category.assoc, Over.w x, ← ht]
    rfl)

theorem push_left (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : (push hw ht x).left = x.left ≫ φ := rfl

def pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : Over.mk t' ⟶ G' :=
  Over.homMk (H.lift x.left t' ((Over.w x).trans ht.symm)) (H.lift_snd _ _ _)

theorem push_pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : push H.w ht (pull H ht x) = x :=
  Over.OverMorphism.ext (H.lift_fst _ _ _)

theorem push_injective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Injective (push H.w ht) := fun x y h =>
  Over.OverMorphism.ext (H.hom_ext (congrArg (fun u => u.left) h) (by rw [Over.w x, Over.w y]))

theorem push_surjective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Surjective (push H.w ht) := fun x => ⟨_, push_pull H ht x⟩

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') (x y : Over.mk t' ⟶ G') :
    push hφ.1.w (t := t' ≫ f) rfl (x * y) = push hφ.1.w rfl x * push hφ.1.w rfl y :=
  Over.OverMorphism.ext (hφ.2 (Over.mk t') x y (push hφ.1.w rfl x) (push hφ.1.w rfl y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') :
    push hφ.1.w (t := t' ≫ f) rfl (1 : Over.mk t' ⟶ G') = 1 := by
  have h := push_mul hφ t' 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem push_comp (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) (x : Over.mk t' ⟶ G') :
    push hw ht (x ≫ a') = push hw ht x ≫ a :=
  Over.OverMorphism.ext (by
    show (x ≫ a').left ≫ φ = (push hw ht x ≫ a).left
    rw [Over.comp_left, Over.comp_left, push_left, Category.assoc, ha, Category.assoc])

theorem isDerivAt0_iff_comp (H : IsPullback φ G'.hom G.hom f) {g : ℕ} {y' : Sp ℂ ⟶ X'}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)} (he : ∀ z, e z ≫ G'.hom = y')
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) (w : Fin g → ℂ) {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') :
    IsDerivAt0 e w v ↔ IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨fun h => FibreDeriv.isDerivAt0_comp h φ, fun h => ?_⟩
  have H₁ := (IsPullback.of_hasPullback G'.hom y').paste_horiz H
  let e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G'.hom y') :=
    fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])
  let v₁ : Sp (DualNumber ℂ) ⟶ pullback G'.hom y' := pullback.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv
  have h1 : ∀ z, e₁ z ≫ pullback.fst _ _ = e z := fun z => pullback.lift_fst _ _ _
  have hv1 : v₁ ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hf1 : (fun z => e₁ z ≫ pullback.fst G'.hom y' ≫ φ) = fun z => e z ≫ φ :=
    funext fun z => by rw [← Category.assoc, h1]
  have key := FibreDeriv.isDerivAt0_of_isPullback H₁ (e := e₁) (fun z => pullback.lift_snd _ _ _)
    (by rw [hf1]; exact hol) (pullback.lift_snd _ _ _) (by rw [hf1, ← Category.assoc, hv1]; exact h)
  have := FibreDeriv.isDerivAt0_comp key (pullback.fst _ _)
  rw [hv1] at this
  simpa only [h1] using this

theorem spMap_fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isExp_iff (hφ : IsGrpPullback G' G f φ) {g : ℕ} (y' : Sp ℂ ⟶ X') (e : (Fin g → ℂ) → (Over.mk y' ⟶ G')) :
    IsExp y' e ↔ IsExp (y' ≫ f) (fun z => push hφ.1.w rfl (e z)) := by
  have H := hφ.1
  have hpe : ∀ z, (push H.w (t := y' ≫ f) rfl (e z)).left = (e z).left ≫ φ := fun z => rfl
  have hes : ∀ z, (e z).left ≫ G'.hom = y' := fun z => Over.w (e z)
  have hol : IsHolTo Set.univ (fun z => (e z).left) ↔ IsHolTo Set.univ (fun z => (e z).left ≫ φ) :=
    ⟨fun h => HolFibre.isHolTo_comp h φ, fun h => HolFibre.isHolTo_of_isPullback H h
      (by simp only [hes]; exact HolFibre.isHolTo_const isOpen_univ y')⟩
  have ht : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (y' ≫ f) :=
    Category.assoc _ _ _
  let pE : (epsPt y' ⟶ G') → (epsPt (y' ≫ f) ⟶ G) := push H.w ht
  have pEi : Function.Injective pE := push_injective H ht
  have pEs : Function.Surjective pE := push_surjective H ht
  have hd : IsHolTo Set.univ (fun z => (e z).left ≫ φ) → ∀ w (v : epsPt y' ⟶ G'),
      IsDerivAt0 (fun z => (e z).left) w v.left ↔ IsDerivAt0 (fun z => (push H.w (t := y' ≫ f) rfl (e z)).left) w (pE v).left :=
    fun h w v => isDerivAt0_iff_comp H hes h w (Over.w v)
  have hbase : ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (pE v).left =
      (push H.w (t := y' ≫ f) rfl (e 0)).left ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := by
    intro v
    refine ⟨fun h => H.hom_ext (by rw [Category.assoc]; exact h) ?_, fun h => ?_⟩
    · rw [Category.assoc, Over.w v, hes]
      show spMap _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y' = y'
      rw [← Category.assoc, spMap_fst_alg, Category.id_comp]
    · show spMap _ ≫ v.left ≫ φ = (e 0).left ≫ φ
      rw [← Category.assoc, h]
  have hinj : Function.Injective (push H.w (t := y' ≫ f) rfl (t' := y')) := push_injective H rfl
  constructor
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' := hol.1 hh
    refine ⟨fun z w => by dsimp only; rw [hadd, push_mul hφ], (push_surjective H rfl).comp hsurj, hh', fun w => ?_,
      fun v hv => ?_⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      refine ⟨pE v, (hd hh' w v).1 hv, fun v' hv' => ?_⟩
      obtain ⟨v', rfl⟩ := pEs v'
      rw [hu v' ((hd hh' w v').2 hv')]
    · obtain ⟨v, rfl⟩ := pEs v
      obtain ⟨w, hw, hu⟩ := hd2 v ((hbase v).1 hv)
      exact ⟨w, (hd hh' w v).1 hw, fun w' hw' => hu w' ((hd hh' w' v).2 hw')⟩
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' : IsHolTo Set.univ (fun z => (e z).left ≫ φ) := hh
    refine ⟨fun z w => hinj (by have h := hadd z w; dsimp only at h; rw [h, push_mul hφ]), fun x => ?_, hol.2 hh', fun w => ?_, fun v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (push H.w rfl x)
      exact ⟨z, hinj hz⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      obtain ⟨v, rfl⟩ := pEs v
      exact ⟨v, (hd hh' w v).2 hv, fun v' hv' => pEi (hu _ ((hd hh' w v').1 hv'))⟩
    · obtain ⟨w, hw, hu⟩ := hd2 (pE v) ((hbase v).2 hv)
      exact ⟨w, (hd hh' w v).2 hw, fun w' hw' => hu w' ((hd hh' w' v).1 hw')⟩

end GlobalTheory.UnifPull

namespace GlobalTheory.UnifPull

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {R R' : Type} [CommRing R]
  [CommRing R'] {σ : R →+* ℂ} {σ' : R' →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {F' : Fam R' O Λ g} {N : ℕ}
  {f : F'.X ⟶ F.X} {φ : F'.A.left ⟶ F.A.left}

theorem unifAt_iff (hφ : IsGrpPullback F'.A F.A f φ) (hact : ∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left)
    (hL : LBIso F'.L (F.L.pull φ)) (heta : ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) (D' : PLat O bar)
    (t : Λ → D'.La) (P : D'.La →+ (Fin g → ℂ)) (y' : Sp ℂ ⟶ F'.X) (hy' : y' ≫ F'.s = spMap σ')
    (hy : (y' ≫ f) ≫ F.s = spMap σ) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F'.A)) :
    UnifAt F' σ' ρ N D' t P y' e' ↔ UnifAt F σ ρ N D' t P (y' ≫ f) (fun z => push hφ.1.w rfl (e' z)) := by
  have hinj : Function.Injective (push hφ.1.w (t := y' ≫ f) rfl (t' := y')) := push_injective hφ.1 rfl
  have hker : ∀ z, push hφ.1.w (t := y' ≫ f) rfl (e' z) = 1 ↔ e' z = 1 := fun z => by
    rw [← push_one hφ y']
    exact hinj.eq_iff
  have hlin : ∀ a z, e' (ρ a *ᵥ z) = e' z ≫ F'.act a ↔
      push hφ.1.w (t := y' ≫ f) rfl (e' (ρ a *ᵥ z)) = push hφ.1.w rfl (e' z) ≫ F.act a := fun a z => by
    rw [← push_comp hφ.1.w rfl (hact a)]
    exact hinj.eq_iff.symm
  have hweil : ∀ (k : ℤ) (x x' : Over.mk y' ⟶ F'.A) (c : Γ(Sp ℂ, ⊤)ˣ), Out.WeilIs F'.A F'.L k x x' c ↔
      Out.WeilIs F.A F.L k (push hφ.1.w (t := y' ≫ f) rfl x) (push hφ.1.w rfl x') c := fun k x x' c =>
    GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ F.A F'.A f φ F.L F'.L F.isLB F'.isLB hφ hL (Over.mk y') k x x' _ _ c
      rfl rfl
  have hunit : ∀ a, push hφ.1.w (t := y' ≫ f) rfl (toUnit (Over.mk y') ≫ F'.eta a) =
      toUnit (Over.mk (y' ≫ f)) ≫ F.eta a := fun a => Over.OverMorphism.ext (by
    rw [push_left, Over.comp_left, Over.comp_left, Category.assoc, heta]
    simp)
  have heta' : ∀ a x, toUnit _ ≫ F'.eta a = x ↔ toUnit _ ≫ F.eta a = push hφ.1.w (t := y' ≫ f) rfl x :=
    fun a x => by
      rw [← hunit]
      exact hinj.eq_iff.symm
  constructor
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy, hP, (isExp_iff hφ y' e').1 hE, fun z => (hker z).trans (hK z), fun a z => (hlin a z).1 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).1 (hW k a b c hk hc), fun a => (heta' a _).1 (hT a)⟩
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy', hP, (isExp_iff hφ y' e').2 hE, fun z => (hker z).symm.trans (hK z), fun a z => (hlin a z).2 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).2 (hW k a b c hk hc), fun a => (heta' a _).2 (hT a)⟩

end GlobalTheory.UnifPull


open GlobalTheory.UnifPull in
theorem GlobalTheory.unifAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  intro O _ bar g ρ R R' _ _ σ σ' Λ F F' N f φ hφ hact hL heta D' t P y' hy' hy
  refine ⟨fun e' he' => ⟨_, (unifAt_iff hφ hact hL heta D' t P y' hy' hy e').1 he', fun z => rfl⟩,
    fun e he => ⟨fun z => pull hφ.1 rfl (e z), ?_, fun z => (hφ.1.lift_fst _ _ _).symm⟩⟩
  have h : (fun z => push hφ.1.w (t := y' ≫ f) rfl (pull hφ.1 rfl (e z))) = e := funext fun z => push_pull hφ.1 rfl (e z)
  exact (unifAt_iff hφ hact hL heta D' t P y' hy' hy _).2 (by rw [h]; exact he)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct Topology

namespace GlobalTheory.HeckeSplitGen

theorem integralFiniteAdelesTensor_eq_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAEF F E = GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  unfold intAEF GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_trivial_modSetF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  intro F E _ _ _ _ _ ν hν
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (GlobalTheory.AdLat.RA F E) := ⟨rfl⟩
  haveI : ContinuousAdd (GlobalTheory.AdLat.RA F E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hsmall := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (by simp)).2
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.finite_order_of_small (infPartF F E) (finPartF F E) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (GlobalTheory.CharFin.hatRing F E) hsmall (GlobalTheory.CharFin.finite_quotient_hatRing F E) ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  rw [integralFiniteAdelesTensor_eq_adelicCompletion_integers] at hr h3
  have hNr : (N : Af F ⊗[F] E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPartF F E (x : AEF F E) ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    have : finPartF F E (x : AEF F E) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => one_mem _, _, ⟨1, rfl⟩,
      by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LUnit

theorem intAt_mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

theorem intAt_one (l : ℕ) : IntAt l 1 := ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one⟩

theorem unitAt_one (l : ℕ) : UnitAt l 1 := ⟨one_ne_zero, intAt_one l, by rw [inv_one]; exact intAt_one l⟩

theorem unitAt_mul {l : ℕ} {a b : ℂ} (ha : UnitAt l a) (hb : UnitAt l b) : UnitAt l (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, intAt_mul ha.2.1 hb.2.1, by rw [mul_inv]; exact intAt_mul ha.2.2 hb.2.2⟩

theorem unitAt_inv {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unitAt_pow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℕ) : UnitAt l (a ^ n) := by
  induction n with
  | zero => simpa using unitAt_one l
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_zpow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℤ) : UnitAt l (a ^ n) := by
  cases n with
  | ofNat n => simpa using unitAt_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact unitAt_inv (unitAt_pow ha _)

theorem unitAt_prod {l : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitAt l (f i)) :
    UnitAt l (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one l
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitAt_neg {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l (-a) := by
  have h1 : UnitAt l (-1) := ⟨by norm_num, ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩,
    ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩⟩
  simpa using unitAt_mul h1 ha

theorem intAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : IntAt l (a ^ h)) : IntAt l a := by
  obtain ⟨n, hn, hi⟩ := ha
  refine ⟨n, hn, IsIntegral.of_pow hh ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have e : ((n : ℂ) * a) ^ (k + 1) = (n : ℂ) ^ k * ((n : ℂ) * a ^ (k + 1)) := by ring
  rw [e]; exact ((isIntegral_natCast (R := ℤ) n).pow _).mul hi

theorem unitAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : UnitAt l (a ^ h)) : UnitAt l a :=
  ⟨fun h0 => ha.1 (by rw [h0, zero_pow hh.ne']), intAt_of_pow hh ha.2.1,
    intAt_of_pow hh (by rw [inv_pow]; exact ha.2.2)⟩

variable {E : Type} [Field E] [NumberField E]

theorem exists_coprime_mul_mem {l : ℕ} (hl : l.Prime) (α : E)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E α ≤ 1) :
    ∃ n : ℕ, n.Coprime l ∧ ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * α := by
  have hal : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨d, hd0, hd⟩ := hal.exists_integral_multiple
  have hD0 : IsIntegral ℤ (((d.natAbs : ℤ)) • α) := by
    rcases Int.natAbs_eq d with e | e
    · rw [← e]; exact hd
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this, neg_smul]; exact hd.neg
  have hD : IsIntegral ℤ ((d.natAbs : E) * α) := by
    have : ((d.natAbs : ℤ) • α) = (d.natAbs : E) * α := by rw [zsmul_eq_mul, Int.cast_natCast]
    rw [← this]; exact hD0
  obtain ⟨e, m, hm, hDm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hd0) l hl.one_lt.ne'
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd hl).2 hm |>.symm, ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun w => ?_
  have hval_nat : ∀ k : ℕ, w.valuation E (k : E) ≤ 1 := fun k => by
    have : (k : E) = algebraMap (𝓞 E) E (k : 𝓞 E) := by simp
    rw [this]; exact w.valuation_le_one _
  by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
  · rw [map_mul]
    exact (mul_le_mul' (hval_nat m) (h w hw)).trans_eq (one_mul _)
  · have h1 : w.valuation E ((l : E) ^ e) = 1 := by
      have : (l : E) = algebraMap (𝓞 E) E (l : 𝓞 E) := by simp
      rw [map_pow, this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]
    have h2 : w.valuation E ((d.natAbs : E) * α) ≤ 1 := by
      have : (d.natAbs : E) * α = algebraMap (𝓞 E) E ⟨_, hD⟩ := rfl
      rw [this]; exact w.valuation_le_one _
    rw [hDm] at h2
    push_cast at h2
    rw [mul_assoc, map_mul, h1, one_mul] at h2
    exact h2

theorem unitAt_embed {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) (σ : E →+* ℂ) :
    UnitAt l (σ α) := by
  have key : ∀ x : E, (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) → IntAt l (σ x) := by
    intro x hx
    obtain ⟨n, hn, b, hb⟩ := exists_coprime_mul_mem hl x hx
    refine ⟨n, hn, ?_⟩
    have : (n : ℂ) * σ x = σ.toIntAlgHom (algebraMap (𝓞 E) E b) := by
      rw [hb]; simp
    rw [this]
    exact (RingOfIntegers.isIntegral_coe b).map _
  refine ⟨by simp, key _ fun w hw => (h w hw).le, ?_⟩
  rw [← map_inv₀]
  exact key _ fun w hw => by rw [map_inv₀, h w hw, inv_one]

end GlobalTheory.CMVal.LUnit

namespace GlobalTheory.CMVal.LUnit

variable {E : Type} [Field E] [NumberField E]

theorem mul_coord' (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem pow_coord (z : Af E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (z ^ n) w = (z w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem val_coord_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((u : Af E) w) = 1 := by
  have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.1 w)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.2 w)
  have h3 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) = 1 := by
    rw [← map_mul, ← mul_coord', Units.mul_inv]
    exact map_one _
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have h4 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) ≤ Valued.v ((u : Af E) w) * 1 := mul_le_mul' le_rfl h2
  rw [h3, mul_one] at h4
  exact absurd h4 (not_le.2 hlt)

theorem modF_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  simp [val_coord_of_mem_hatOUnits hu]

theorem modF_pow (y : (Af E)ˣ) (n : ℕ) : modF (y ^ n) = modF y ^ n := by
  induction n with
  | zero =>
    unfold modF
    simp only [pow_zero, Units.val_one]
    exact finprod_eq_one_of_forall_eq_one fun w => by
      have : (1 : Af E) w = 1 := rfl
      rw [this, map_one]; simp
  | succ n ih => rw [pow_succ, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, ih, pow_succ]

theorem unitAt_norm {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) :
    UnitAt l (((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ)) := by
  have h1 : UnitAt l (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) := by
    have e : (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) = algebraMap ℚ ℂ (Algebra.norm ℚ (α : E)) := by simp
    rw [e, Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact unitAt_prod _ _ fun σ _ => unitAt_embed hl α h σ.toRingHom
  rcases abs_choice ((Algebra.norm ℚ (α : E) : ℝ)) with e | e
  · rw [e]; exact h1
  · rw [e, Complex.ofReal_neg]; exact unitAt_neg h1

end GlobalTheory.CMVal.LUnit


open GlobalTheory.CMVal.LUnit in
theorem GlobalTheory.CMVal.value_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (l : ℕ), c ≠ ⊥ → l.Prime →
    HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ,
    (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v ((y : Af E) w) = 1) →
    UnitAt l ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) := by
  intro E _ _ _ I _ φ _ s κ c χ l hc hl hinf hχ y hy
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)

  have hval : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1 := by
    intro w hw
    have e1 : Units.map (algebraMap E (Af E)).toMonoidHom α = y ^ h * u⁻¹ := eq_mul_inv_of_mul_eq hpu
    have e2 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom α : (Af E)ˣ) : Af E) w) = w.valuation E (α : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (α : E)
    rw [← e2, e1, Units.val_mul, mul_coord', Units.val_pow_eq_pow_val, pow_coord, map_mul, map_pow, hy w hw, one_pow,
      one_mul, val_coord_of_mem_hatOUnits (inv_mem hu) w]

  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hm : modF y ^ h = (|(Algebra.norm ℚ (α : E) : ℝ)|)⁻¹ := by
    rw [← modF_pow, ← hpu, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, modF_of_mem_hatOUnits hu, mul_one,
      (GlobalTheory.CMVal.modF_mul_pos_principal E).2.2]
  have hpow : ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) ^ h =
      ((χ.inf α : ℂˣ) : ℂ)⁻¹ * ((((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ))⁻¹) ^ s := by
    rw [mul_pow, hf, ← Complex.ofReal_pow, ← pow_mul, mul_comm s h, pow_mul, hm]
    push_cast
    ring
  refine unitAt_of_pow hpos ?_
  rw [hpow]
  refine unitAt_mul (unitAt_inv ?_) (unitAt_pow (unitAt_inv (unitAt_norm hl α hval)) s)
  rw [(hasInfRatio_iff χ φ _).1 hinf α]
  refine unitAt_prod _ _ fun i _ => unitAt_zpow (unitAt_mul (unitAt_embed hl α hval (φ i)) (unitAt_inv ?_)) _
  exact unitAt_embed hl α hval ((starRingEnd ℂ).comp (φ i))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.WeilComplexUnique

theorem weilIs_unitOn_unique_complex : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (y : Sp ℂ ⟶ X) (k : ℤ) (x x' : Over.mk y ⟶ G) (c c' : ℂˣ), Out.WeilIs G L k x x' (unitOn c) → Out.WeilIs G L k x x' (unitOn c') → c = c' := by
  intro X G _ _ g _ _ L hL y k x x' c c' h h'
  exact GlobalTheory.weilIs_unique_fieldPoint X G L hL ℂ y k x x' c c' h h'

end GlobalTheory.WeilComplexUnique
end

