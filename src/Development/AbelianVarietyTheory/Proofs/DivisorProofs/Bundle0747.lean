module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaRestrictFiniteAbelianUnramifiedEqOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.InertiaRestrict

theorem restrict_eq_one : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L → ∀ (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, σ ∈ ReciprocityTheory.Gal.Ine (F := K) A → haveI := h.isGalois; AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) = 1 := by
  intro K _ _ Ω _ _ _ e L h v hv A hA σ hσ
  haveI := h.isGalois
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  have hint : ∀ y : 𝓞 L, e.symm ((y : L) : AlgebraicClosure K) ∈ A := by
    intro y
    have h1 : IsIntegral ℤ (e.symm ((y : L) : AlgebraicClosure K)) :=
      map_isIntegral_int ((e.symm : AlgebraicClosure K →+* Ω).comp (algebraMap L (AlgebraicClosure K)))
        y.isIntegral_coe
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (h1.tower_top)
    rw [← ha]
    exact a.2
  let φ : 𝓞 L →+* A :=
    { toFun := fun y => ⟨e.symm ((y : L) : AlgebraicClosure K), hint y⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ
  have hmem : ∀ y : 𝓞 L, y ∈ Q ↔ A.valuation (e.symm ((y : L) : AlgebraicClosure K)) < 1 := fun y =>
    ValuationSubring.valuation_lt_one_iff A (φ y)
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI hQo : Q.LiesOver v.asIdeal := by
    constructor
    ext x
    rw [Ideal.under, Ideal.mem_comap, hmem, ← hA x]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := by
      first
        | rfl
        | (rw [RingOfIntegers.algebraMap_coe]; rfl)
        | simp [IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)]
    rw [this, AlgEquiv.commutes]
  have hram : Q.ramificationIdx (𝓞 K) = 1 := hv Q hQp hQo
  have hcard : Nat.card (Q.inertia (L ≃ₐ[K] L)) = 1 := by
    have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
    have hpr : (Q.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ Q
    have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (Q.under (𝓞 K)) Q
    rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 K)) Q (L ≃ₐ[K] L), hram] at hc
  have hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ := Subgroup.card_eq_one.1 hcard
  have hin : AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) ∈ Q.inertia (L ≃ₐ[K] L) := by
    refine AddSubgroup.mem_inertia.mpr fun y => ?_
    change _ ∈ Q
    rw [hmem]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y - y : 𝓞 L) : L) : AlgebraicClosure K)
        = e (σ (e.symm ((y : L) : AlgebraicClosure K))) - ((y : L) : AlgebraicClosure K) := by
      have h3 : ((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) =
          AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) (y : L) := rfl
      simp only [map_sub, h3, AlgEquiv.restrictNormalHom_apply]
      have h4 := AlgEquiv.restrictNormalHom_apply L ((e.symm.trans σ).trans e) (y : L)
      rw [AddSubgroupClass.coe_sub, h4]
      rfl
    rw [h2, map_sub, AlgEquiv.symm_apply_apply]
    exact hσ.2 _ ((A.valuation_le_one_iff _).2 (hint y))
  rw [hbot] at hin
  exact hin

end GlobalTheory.InertiaRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMTypeCard

theorem bijective_mk_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  refine ⟨fun i j hij => ?_, fun w => ?_⟩
  · obtain ⟨k, -, hk⟩ := h (φ j)
    have h1 : j = k := hk j (Or.inl rfl)
    have h2 : i = k := hk i (by
      rcases InfinitePlace.mk_eq_iff.1 hij with e | e
      · exact Or.inl e.symm
      · exact Or.inr e.symm)
    rw [h1, h2]
  · obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    rcases hi with e | e
    · simp only [← e, InfinitePlace.mk_embedding]
    · have := congrArg InfinitePlace.mk e
      rw [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] at this
      exact this.symm

theorem card_eq_finrank_of_isCMType : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2),
    Fintype.card I = Module.finrank K E := by
  intro K E _ _ _ _ _ _ I _ φ hφ h2
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (bijective_mk_of_isCMType hφ)
  have hE : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have hr : NumberField.InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    omega
  have hKE : Module.finrank ℚ E = Module.finrank ℚ K * Module.finrank K E :=
    (Module.finrank_mul_finrank ℚ K E).symm
  rw [h2] at hKE
  omega

end GlobalTheory.CMTypeCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.Div

theorem resG_eq_inv_mul_appLE {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {φ : X' ⟶ X}
    (w : LB.Iso H' (H.pull φ)) (k : H.ι) (k' : H'.ι) (a : Γ(X, H.U k)) (b : Γ(X', H'.U k'))
    (h : ∀ z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ a = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ b) :
    resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b =
      ((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val *
        (φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
          (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a := by
  apply fn_ext
  intro x hx
  have hk : φ x ∈ H.U k := (GlobalTheory.Cartier.pull_U H φ _).le hx.1
  have hx' : x ∈ H'.U k' := hx.2
  have e := h x hk hx'
  have h1 : gs (𝟙 X') x _ (resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b) =
      gs (𝟙 X') x _ b := gs_res (𝟙 X') x inf_le_right hx b
  have h2 : gs (𝟙 X') x _ ((φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
      (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a) = gs φ x _ a := by
    have := gs_res (𝟙 X') x (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le) hx ((φ.app (H.U k)).hom a)
    refine Eq.trans ?_ (this.trans ((gs_pull (𝟙 X') φ x (H.U k) hk a).trans (by rw [Category.id_comp])))
    rfl
  have h3 : gs (𝟙 X') x _ (((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val) =
      ((Geo.Tor.gw w (𝟙 _) x k k')⁻¹).val := by
    rw [gs_unit (𝟙 X') x _ hx, map_inv]
    rfl
  rw [h1, gs_mul (𝟙 X') x _ hx, h2, h3, e, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem isClosedImmersion_of_veryAmpleBy_compat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  intro R _ X f H n s hH hs X' f' H' s' φ w hH' hs' hf _ hrel
  subst hf
  obtain ⟨hc, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hs
  obtain ⟨hc', hci'⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff (φ ≫ f) s').1 hs'
  have heq : GlobalTheory.ProjSpace.toProj (φ ≫ f) s' hc' = φ ≫ GlobalTheory.ProjSpace.toProj f s hc := by
    refine GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hc φ hc' fun z => ?_
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact ⟨(H.pull φ).U (fun _ => k) ⊓ H'.U k', ⟨(GlobalTheory.Cartier.pull_U H φ _).ge hk, hk'⟩, k,
      inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le, k', inf_le_right, _,
      fun j => resG_eq_inv_mul_appLE w k k' _ _ fun y hy hy' => hrel j y k k' hy hy'⟩
  have : IsClosedImmersion (φ ≫ GlobalTheory.ProjSpace.toProj f s hc) := heq ▸ hci'
  exact IsClosedImmersion.of_comp_isClosedImmersion φ (GlobalTheory.ProjSpace.toProj f s hc)

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isGaloisCover_of_isPullback {X Y X' Y' : Scheme.{0}} {Ga Ga' : Type} [Group Ga] [Group Ga']
    {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y} {ρ' : Ga' → (X' ⟶ X')} {π' : X' ⟶ Y'} {u : X' ⟶ X} {v : Y' ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (one' : ρ' 1 = 𝟙 X') (mul' : ∀ a c, ρ' (a * c) = ρ' a ≫ ρ' c) (inj' : Function.Injective ρ')
    (hπ : ∀ a, ρ' a ≫ π' = π')
    (up : ∀ a', ∃ a, ρ' a' ≫ u = u ≫ ρ a) (down : ∀ a, ∃ a', ρ' a' ≫ u = u ≫ ρ a) :
    GlobalTheory.ZM.IsGaloisCover Ga' ρ' π' := by
  refine
    { finite := ?_
      one := one'
      mul := mul'
      inv := hπ
      fin := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
      etale := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
      onto := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
      fibre := ?_ }
  · have := h.finite
    choose σ hσ using up
    refine Finite.of_injective σ fun a c e => inj' ?_
    exact hp.hom_ext (by rw [hσ, hσ, e]) (by rw [hπ, hπ])
  · intro K _ _ y y' e
    obtain ⟨a, ha, ha'⟩ := h.fibre K (y ≫ u) (y' ≫ u) (by simp only [Category.assoc, hp.w, reassoc_of% e])
    obtain ⟨a', ea'⟩ := down a
    have ex : y ≫ ρ' a' = y' := hp.hom_ext
      (by rw [Category.assoc, ea', ← Category.assoc, ha])
      (by rw [Category.assoc, hπ, e])
    refine ⟨a', ex, fun b' hb' => inj' ?_⟩
    obtain ⟨b, eb⟩ := up b'
    have hb'' : y ≫ ρ' b' = y' := hb'
    have hb : b = a := ha' b (by show (y ≫ u) ≫ ρ b = y' ≫ u; rw [Category.assoc, ← eb, ← Category.assoc, hb''])
    subst hb
    exact hp.hom_ext (by rw [eb, ea']) (by rw [hπ, hπ])

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  show 𝟙 A * (toUnit A ≫ 1) = 𝟙 A
  rw [MonObj.comp_one, _root_.mul_one]

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  have e : transl a ≫ transl c = transl a * (toUnit A ≫ c) := by
    show transl a ≫ (𝟙 A * (toUnit A ≫ c)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (transl a ≫ toUnit A) (toUnit A)]
  rw [e]
  show 𝟙 A * (toUnit A ≫ (a * c)) = (𝟙 A * (toUnit A ≫ a)) * (toUnit A ≫ c)
  rw [MonObj.comp_mul, _root_.mul_assoc]

theorem transl_injective {S : Scheme.{0}} {A : Over S} [GrpObj A] {a c : 𝟙_ (Over S) ⟶ A}
    (h : (transl a).left = (transl c).left) : a = c := by
  have h' : transl a = transl c := Over.OverMorphism.ext h
  rw [← one_comp_transl a, h', one_comp_transl]

theorem grpScheme_square_hom_ext {S : Scheme.{0}} {A : Over S} {X : Scheme.{0}} (u u' : X ⟶ (A ⊗ A).left)
    (h₁ : u ≫ (fst A A).left = u' ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = u' ≫ (snd A A).left) : u = u' := by
  have hw : u' ≫ (A ⊗ A).hom = u ≫ (A ⊗ A).hom := by
    rw [← Over.w (fst A A), ← Category.assoc, ← h₁, Category.assoc]
  let U : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u rfl
  let U' : Over.mk (u ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk u' hw
  have : U = U' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂)
  exact congrArg (fun z => z.left) this

theorem grpSchemeSquareProductMap_comp_fst {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (fst A' A').left = (fst A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_fst, Over.comp_left]

theorem grpSchemeSquareProductMap_comp_snd {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') : sq2 ψ ≫ (snd A' A').left = (snd A A).left ≫ ψ.left := by
  show (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left ≫ _ = _
  rw [← Over.comp_left, lift_snd, Over.comp_left]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h = n • GlobalTheory.CechPic.cls L hL := by
  unfold GlobalTheory.UPel.HT.Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hL]
  simp [GlobalTheory.CechPic.pull_id]

end GlobalTheory.UPel.HT.Hecke.PullHecke

namespace GlobalTheory.UPel.HT.Hecke.PullHecke

theorem isHecke_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R)
    (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s))
    (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f →
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  intro p _ D R _ b g c k N _ _ _ S S' s f o o' ψ o₁ o₁' hH m m'
  obtain ⟨hmon, hlin, heta, hgal, ⟨hP⟩, hdvd⟩ := hH
  have w : (m.φ ≫ ψ.left) ≫ o'.A.hom = o₁.A.hom ≫ f := by
    rw [Category.assoc, Over.w]; exact m.cart.1.w
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom w) (m'.cart.1.lift_snd _ _ _)
  have hψ₁ : ψ₁.left ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have ext' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A), x.left ≫ m'.φ = y.left ≫ m'.φ → x = y := fun x y e =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext e (by rw [Over.w, Over.w]))

  have pa : ∀ {T : Over S'} (x : T ⟶ o₁.A), pushPt m'.cart.1.w (x ≫ ψ₁) = pushPt m.cart.1.w x ≫ ψ := fun x =>
    Over.OverMorphism.ext (by
      show (x ≫ ψ₁).left ≫ m'.φ = (x.left ≫ m.φ) ≫ ψ.left
      rw [Over.comp_left, Category.assoc, hψ₁, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ o₁.A),
      pushPt m.cart.1.w (x * y) = pushPt m.cart.1.w x * pushPt m.cart.1.w y := fun x y => map_mul (pushHom m.cart _) x y
  have pm' : ∀ {T : Over S'} (x y : T ⟶ o₁'.A),
      pushPt m'.cart.1.w (x * y) = pushPt m'.cart.1.w x * pushPt m'.cart.1.w y := fun x y => map_mul (pushHom m'.cart _) x y
  have inj' : ∀ {T : Over S'} {x y : T ⟶ o₁'.A}, pushPt m'.cart.1.w x = pushPt m'.cart.1.w y → x = y := fun e =>
    ext' _ _ (congrArg (fun z => z.left) e)
  haveI := hmon
  have hmon₁ : IsMonHom ψ₁ := by
    refine isMonHom_of_mul ψ₁ fun T x y => ?_
    apply inj'
    rw [pa, pm, MonObj.mul_comp, ← pa, ← pa, pm']

  have tc : ∀ z, (transl (o₁.eta z)).left ≫ m.φ = m.φ ≫ (transl (o.eta z)).left := by
    intro z
    have hu : pushPt m.cart.1.w (toUnit o₁.A ≫ o₁.eta z) = toUnit _ ≫ o.eta z := Over.OverMorphism.ext (by
      show (toUnit o₁.A ≫ o₁.eta z).left ≫ m.φ = (toUnit (Over.mk (o₁.A.hom ≫ f)) ≫ o.eta z).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.eta]
      simp)
    have e : pushPt m.cart.1.w (transl (o₁.eta z)) = pushPt m.cart.1.w (𝟙 o₁.A) ≫ transl (o.eta z) := by
      show pushPt m.cart.1.w (𝟙 o₁.A * (toUnit o₁.A ≫ o₁.eta z)) =
        pushPt m.cart.1.w (𝟙 o₁.A) ≫ (𝟙 o.A * (toUnit o.A ≫ o.eta z))
      rw [pm, hu, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (_ ≫ toUnit o.A) (toUnit _)]
    have e' : (transl (o₁.eta z)).left ≫ m.φ = ((𝟙 o₁.A : o₁.A ⟶ o₁.A).left ≫ m.φ) ≫ (transl (o.eta z)).left :=
      congrArg (fun z => z.left) e
    rw [e', Over.id_left, Category.id_comp]
  have hp : IsPullback m.φ ψ₁.left ψ.left m'.φ := by
    refine IsPullback.of_bot ?_ hψ₁.symm m'.cart.1
    rw [Over.w ψ₁, Over.w ψ]; exact m.cart.1
  refine ⟨ψ₁, hmon₁, fun c' => ?_, fun x => ?_, ?_, ?_, hdvd⟩
  · apply ext'
    have h₀ := congrArg (fun z => m.φ ≫ z.left) (hlin c')
    simp only [Over.comp_left, Category.assoc] at h₀ ⊢
    rw [hψ₁, m'.act, reassoc_of% hψ₁, reassoc_of% (m.act c')]
    exact h₀
  · apply ext'
    rw [m'.eta, heta]
    simp only [Over.comp_left, Category.assoc]
    rw [hψ₁, reassoc_of% (m.eta (g x))]
  · refine isGaloisCover_of_isPullback hgal hp ?_ (fun a c => ?_) (fun a c e => Subtype.ext (transl_injective e))
      (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · show (transl 1).left = _
      rw [transl_one, Over.id_left]
    · show (transl (a.1 * c.1)).left = _
      rw [transl_mul, Over.comp_left]
    · obtain ⟨h, x, rfl⟩ := a
      have hi : (transl (o.eta (N • g x))).left ≫ ψ.left = ψ.left := hgal.inv ⟨_, mem_heckeSub o g N x⟩
      show (transl (o₁.eta (N • g x))).left ≫ ψ₁.left = ψ₁.left
      refine m'.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, hψ₁, ← Category.assoc, tc, Category.assoc, hi]
      · rw [Category.assoc, Over.w ψ₁, Over.w]
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o g N x⟩, tc _⟩
    · obtain ⟨h, x, rfl⟩ := a
      exact ⟨⟨_, mem_heckeSub o₁ g N x⟩, tc _⟩
  · have hs1 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
    have hs2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
    have hn₀ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    have hn₁ : (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · rw [Category.assoc, m'.sq.1, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_fst,
          ← Category.assoc m.φ₂, hs1, Category.assoc]
      · rw [Category.assoc, m'.sq.2, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, Category.assoc, grpSchemeSquareProductMap_comp_snd,
          ← Category.assoc m.φ₂, hs2, Category.assoc]
    have c₁ : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have c₁' : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) :=
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have c₀ : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = (k ^ 2 / c) • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB _ (pull_isLB o'.isLB _),
        ← (GlobalTheory.CechPic.cls_eq_iff hn₀ (pull_isLB o'.isLB _)).2 hP, cls_heckePow o.isLB]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hn₁ (pull_isLB o₁'.isLB _)).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB, c₁, c₁', ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, c₀, map_nsmul]

end GlobalTheory.UPel.HT.Hecke.PullHecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem isLattice_of_eq_span_frac_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) (M N : Submodule (𝓞 K) V)
    (h : M = Submodule.span (𝓞 K) {x | ∃ a ∈ I, ∃ y ∈ N, x = (a : K) • y})
    (hM : Submodule.IsLattice K M) : Submodule.IsLattice K N := by
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ (0 : K) := by
    by_contra hc
    push_neg at hc
    exact hI (FractionalIdeal.eq_zero_iff.2 hc)
  refine ⟨?_, ?_⟩
  · let f : V →ₗ[𝓞 K] V := (LinearMap.lsmul K V a).restrictScalars (𝓞 K)
    have hf : Function.Injective f := fun x y hxy => smul_right_injective V ha0 hxy
    have hle : N.map f ≤ M := by
      rintro _ ⟨y, hy, rfl⟩
      rw [h]
      exact Submodule.subset_span ⟨a, haI, y, hy, rfl⟩
    have hfg : (N.map f).FG := Submodule.FG.of_le hM.fg hle
    exact Submodule.fg_of_fg_map_injective f hf hfg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isLattice_comap_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W]
    [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (e : W ≃ₗ[K] V) (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.comap ((e : W →ₗ[K] V).restrictScalars (𝓞 K))) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective ((e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.injective ?_
    rw [Submodule.map_comap_eq_of_surjective
      (f := (e : W →ₗ[K] V).restrictScalars (𝓞 K)) e.surjective]
    exact hN.fg
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

theorem nuLat_comap_isLattice : ∀ (D : D7) (L : SizeData₂ D), Formalism.BasicNotions.DV.NprimeDef D L → ∀ u, Submodule.IsLattice D.what₂.LL (D.div.Nu u).L → ∀ (d : ℕ) (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Submodule.IsLattice D.what₂.LL ((L.NuLat u).comap ((e : (Fin d → D.what₂.LL) →ₗ[D.what₂.LL] (D.div.Nu u).V).restrictScalars (𝓞 D.what₂.LL))) := by
  intro D L hdef u hL d e
  have hI : Formalism.BasicNotions.DV.Iu D L u ≠ 0 := by
    unfold Formalism.BasicNotions.DV.Iu
    rw [Finset.prod_ne_zero_iff]
    intro w _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq w).ne_bot)
  exact isLattice_comap_equiv e _
    (isLattice_of_eq_span_frac_smul (Formalism.BasicNotions.DV.Iu D L u) hI _ _ (hdef u) hL)

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenDiagonalSliceLevelSubgroup
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem isOpen_levelSub : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E))
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
      IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  intro E _ _ a r hr t L hL
  have hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_val).matrix_reindex _ _
    · have e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹) := by
        intro l; rw [← map_inv]; rfl
      simp_rw [e]
      show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_coe_inv).matrix_reindex _ _
  have hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t :=
    (continuous_const.mul hblk).mul continuous_const
  have hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) =
      (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E))) := by
    ext l
    simp only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [← e]; simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  rw [hs]
  exact hL.preimage hc

end GlobalTheory.SliceTwo
end

