module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
section
noncomputable section

namespace GlobalTheory.MulDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_eq_one_of_kTriv_pull {S S' : Scheme.{0}} {f : S' ⟶ S}
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L')
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A)
    (hx : ∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen)
    {R' : CommRingCat.{0}} (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S') (sq : g ≫ t = t' ≫ f) :
    g ≫ x.left = g ≫ (1 : Over.mk t ⟶ A).left := by
  obtain ⟨w, hw⟩ := hw
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact congrArg (fun q => q.left) e₂

theorem kTriv_of_locally {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (H : ∀ s : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S), IsOpenImmersion f ∧ IsAffineHom f ∧ s ∈ Set.range f ∧
      KTriv ((Over.pullback f).obj A) (L.pull (pullback.fst A.hom f))) : KTriv A L := by
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨S', f, h₁, h₂, ⟨s, hs⟩, hK⟩ := H (t p)
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let g := (pullback t f).isoSpec.inv ≫ pullback.fst t f
  have e := comp_eq_one_of_kTriv_pull (isGrpPullback_pullback A f) hL (LB.isLB_pull hL _)
    (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)) hK t x hx g ((pullback t f).isoSpec.inv ≫ pullback.snd t f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have e' : pullback.fst t f ≫ x.left = pullback.fst t f ≫ (1 : Over.mk t ⟶ A).left := by
    rw [← cancel_epi (pullback t f).isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact e
  refine ⟨(pullback.fst t f).opensRange, ?_, ?_⟩
  · show p ∈ Set.range (pullback.fst t f)
    rw [Scheme.Pullback.range_fst]
    exact ⟨s, hs⟩
  · rw [← cancel_epi (pullback.fst t f).isoOpensRange.hom, ← Category.assoc, ← Category.assoc]
    erw [Scheme.Hom.isoOpensRange_hom_ι]
    exact e'

theorem kTriv_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {L L' : LB A.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso L L') (hK : KTriv A L) : KTriv A L' := by
  obtain ⟨w, hw⟩ : LBIso L' (L.pull (Iso.refl A).hom.left) :=
    h.symm.chartPull (Geo.Tor.chartPullId L') (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl)
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  exact kTriv_pull (isGrpPullback_of_iso (Iso.refl A)) hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.MulDescent

namespace GlobalTheory.MulDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_polarisation_of_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro h₁ h₂ R _ _ _ A _ g m M P pt hA hg hm hu hM hamp hP hpt hbas hfib
  obtain ⟨L, hL, hrig, hsym, hLa, hiso⟩ := GlobalTheory.OddDescent.exists_descended h₁ h₂ R A g m M pt hA hg hm hu hM hamp hpt hbas (by
    intro f hf
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    by_contra hn
    obtain ⟨p, hp, hp', -, hfp⟩ := hP q f hq hn
    exact hfp (hf p (hfib p hp) hp'))
  refine ⟨L, hL, hrig, hsym, hLa, kTriv_of_locally hL fun s => ?_, hiso⟩
  have hs : (s : PrimeSpectrum R).asIdeal.IsPrime := (s : PrimeSpectrum R).isPrime
  obtain ⟨p, hp, -, hle, -⟩ := hP (s : PrimeSpectrum R).asIdeal 1 hs
    (fun h => hs.ne_top ((Ideal.eq_top_iff_one _).2 h))
  obtain ⟨K, _, _, x, Pl, φ, hker, hφ, hw⟩ := hfib p hp
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x Pl.A φ hA hL hLa hφ
    (kTriv_of_lbIso Pl.isLB (LB.isLB_pull hL _) (hiso K x Pl φ hφ hw) Pl.ktriv)
  have hfs : f ∉ (s : PrimeSpectrum R).asIdeal := fun h => hf (by
    have := hle h
    rwa [← hker, RingHom.mem_ker] at this)
  have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨_, spMap (algebraMap R (Localization.Away f)), ho, inferInstance, ?_,
    H (Localization.Away f) (algebraMap R _) _ _ (IsLocalization.Away.algebraMap_isUnit f)
      (isGrpPullback_pullback A _)⟩
  have : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hfs
  exact this

end GlobalTheory.MulDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelTheta

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {ψ : Y ⟶ X} (φ : Z ⟶ Y) {χ : Z ⟶ X}
    (H : LBIso M (L.pull ψ)) (e : χ = φ ≫ ψ) : LBIso (M.pull φ) (L.pull χ) :=
  H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M φ φ rfl)
    (chartPullSame L (fun _ : PUnit => χ) (fun _ : PUnit => ψ) (fun _ => 1) φ (fun _ => e))

theorem pow_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x' : Out.baseOver S' ⟶ G') (x : Out.baseOver S ⟶ G)
    (e : x'.left ≫ φ = f ≫ x.left) (m : ℕ) : (x' ^ m).left ≫ φ = f ≫ (x ^ m).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e₁ : pushHom h _ x' = preHom U x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ m) = preHom U (x ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e₂

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def Above {S S' : Scheme.{0}} (P : Out.PolAV S) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (m : ℕ) {s' : S' ⟶ Sp o} (t : TObj g k J b s') (f : S' ⟶ S) (ψ : t.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback t.A P.A f ψ ∧ LBIso t.L (P.L.pull ψ) ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ m).left ≫ ψ = f ≫ (Q i).left

theorem Above.comp {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s'}
    {u : TObj g k J b s''} {f : S' ⟶ S} {ψ : t.A.left ⟶ P.A.left} (h : Above P act Q m t f ψ) {f' : S'' ⟶ S'}
    {φ : u.A.left ⟶ t.A.left} (h₁ : IsGrpPullback u.A t.A f' φ) (h₂ : LBIso u.L (t.L.pull φ))
    (h₃ : ∀ i, (u.pt i).left ≫ φ = f' ≫ (t.pt i).left) (h₄ : ∀ j, (u.act j).left ≫ φ = φ ≫ (t.act j).left) :
    Above P act Q m u (f' ≫ f) (φ ≫ ψ) := by
  refine ⟨h₁.comp h.1, LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB P.isLB _) h₂
    (lbIso_pull_comp φ h.2.1 rfl), fun i => ?_, fun i => ?_⟩
  · rw [← Category.assoc, h₄, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, pow_push h₁ _ _ (h₃ i), Category.assoc, h.2.2.2, Category.assoc]

theorem Above.compare {S S' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {u u' : TObj g k J b s'}
    {f : S' ⟶ S} {ψ : u.A.left ⟶ P.A.left} {ψ' : u'.A.left ⟶ P.A.left} (h : Above P act Q m u f ψ)
    (h' : Above P act Q m u' f ψ') :
    ∃ χ : u'.A.left ⟶ u.A.left, χ ≫ ψ = ψ' ∧ IsGrpPullback u'.A u.A (𝟙 _) χ ∧ LBIso u'.L (u.L.pull χ) ∧
      (∀ i, (u'.pt i ^ m).left ≫ χ = (u.pt i ^ m).left) ∧ ∀ j, (u'.act j).left ≫ χ = χ ≫ (u.act j).left := by
  have hp := h.1.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom h'.1.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  refine ⟨χ, e₁, h.1.cancel (h'.1.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id]),
    LBIso.trans u'.isLB (pull_isLB P.isLB _) (pull_isLB u.isLB _) h'.2.1
      (lbIso_pull_comp χ h.2.1 e₁.symm).symm, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.2, h.2.2.2]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.1, Category.assoc, h.2.2.1, ← Category.assoc, e₁]
    · rw [Category.assoc, e₂, Over.w, Category.assoc, Over.w, e₂]

theorem exists_level_with_theta_point : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  intro hL hL2 g n j J hn hodd hj o _ b R _ _ _ β v P act Q hP hdense
  have hn2 : 2 ≤ n := hn.two_le
  have hpos : 0 < n ^ j := pow_pos hn.pos j
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h3 : 3 ≤ n ^ j := by
    have h4 : 2 ^ 2 ≤ n ^ j := (Nat.pow_le_pow_left hn2 2).trans (Nat.pow_le_pow_right hn.pos hj)
    omega
  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, hab, huniv⟩ := GlobalTheory.exists_finiteEtale_level_cover hL hL2 o g (n ^ j) J b R β P act Q hpos hP
  have hab' : Above P act Q (n ^ j) t₁ (spMap (algebraMap R R₁)) ψ₁ := hab
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨K, _, _, x, t', ψ, hker, hth, -⟩, -, hqp, -⟩ :=
      hdense q 1 hq.isPrime (fun h => hq.ne_top ((Ideal.eq_top_iff_one _).2 h))
    obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh hL hL2 o g (n ^ j) J b _ _ t' n K (𝟙 _) _ ⊥ hn2 hdvd hth Ideal.isPrime_bot 0
    apply hc
    have : v (0 + (n ^ j / n) • c) ∈ RingHom.ker x := hker ▸ hqp (hle (Ideal.subset_span ⟨_, rfl⟩))
    exact this
  have hspan₁ : Ideal.span (Set.range fun a => algebraMap R R₁ (v a)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R₁)) hspan
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff hL hL2 o g (n ^ j) J b R₁ _ t₁ _ hodd.pow h3 hspan₁

  have hth : ∀ (R' : Type) [CommRing R'] (x : R →+* R') (y : R₁ →+* R') (s' : Sp R' ⟶ Sp o)
      (t' : TObj g ((n ^ j) ^ 2) J b s'), y.comp (algebraMap R R₁) = x → TMap t' t₁ (spMap y) →
      (t'.HasTh (𝟙 _) (fun a => x (v a)) ↔ ∀ r ∈ 𝔞, y r = 0) := by
    intro R' _ x y s' t' e hm
    subst e
    rw [GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ t' _ R' _ _ hm, Category.id_comp]
    exact h𝔞 R' y

  have huniq : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = x → y'.comp (algebraMap R R₁) = x → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) →
      y = y' := by
    intro K _ _ x y y' e e' k k'
    have d : spMap y ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e]
    have d' : spMap y' ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e']
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y) t₁ (by rw [← Category.assoc, d])
    obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y') t₁ (by rw [← Category.assoc, d'])
    have T := (hth K x y _ u e hu).2 k
    have T' := (hth K x y' _ u' e' hu').2 k'
    obtain ⟨φ, a₁, a₂, a₃, a₄⟩ := id hu
    obtain ⟨φ', a₁', a₂', a₃', a₄'⟩ := id hu'
    have A := hab'.comp a₁ a₂ a₃ a₄
    have A' := hab'.comp a₁' a₂' a₃' a₄'
    rw [d] at A
    rw [d'] at A'
    obtain ⟨χ, c₀, c₁, c₂, c₃, c₄⟩ := A.compare A'
    have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ T T'
    have hχ : TMap u' u (𝟙 _) := ⟨χ, c₁, c₂, fun i => by rw [c₅, Category.id_comp], c₄⟩
    have hm : TMap u' t₁ (spMap y) := by
      have := ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ u u').2 _ _ hu).1 hχ
      rwa [Category.id_comp] at this
    refine (huniv K x u' (φ' ≫ ψ₁) A').unique ⟨e, fun i => ?_, hm⟩ ⟨e', fun i => ?_, hu'⟩
    · rw [← c₀, ← Category.assoc, c₅, ← Category.assoc, a₃, Category.assoc]
    · rw [← Category.assoc, a₃', Category.assoc]
  have hcomp : (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) = algebraMap R (R₁ ⧸ 𝔞) := rfl
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R 𝔞) Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap R (R₁ ⧸ 𝔞)) := by
    refine GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point R (R₁ ⧸ 𝔞) _ hdense ?_
    rintro q ⟨K, _, _, x, t', ψ, hker, T, A⟩
    obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y k, ?_, fun z hz => ?_⟩
    · exact e
    · have := huniq K x (z.comp (Ideal.Quotient.mk 𝔞)) y hz e
        (fun r hr => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]) k
      exact Ideal.Quotient.ringHom_ext (this.trans (by ext r; rfl))
  let ε : R ≃+* R₁ ⧸ 𝔞 := RingEquiv.ofBijective _ hbij
  let ρ : R₁ →+* R := (ε.symm : R₁ ⧸ 𝔞 →+* R).comp (Ideal.Quotient.mk 𝔞)
  have hρ : ρ.comp (algebraMap R R₁) = RingHom.id R := RingHom.ext fun r => ε.symm_apply_apply r
  have hρ' : ∀ r, r - algebraMap R R₁ (ρ r) ∈ 𝔞 := fun r =>
    Ideal.Quotient.eq.1 (ε.apply_symm_apply (Ideal.Quotient.mk 𝔞 r)).symm
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap β) (spMap ρ) t₁
    (by rw [← Category.assoc, spMap_comp, hρ, spMap_id, Category.id_comp])
  refine ⟨t, (hth R (RingHom.id R) ρ _ t hρ ht).2 fun r hr => ?_, fun K _ _ x t' ψ T A => ?_⟩
  · show ε.symm (Ideal.Quotient.mk 𝔞 r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  · obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    have hy : x.comp ρ = y := RingHom.ext fun r => by
      have := k _ (hρ' r)
      rw [map_sub, sub_eq_zero] at this
      rw [this, ← e]; rfl
    refine ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ t t').2 _ _ ht).2 ?_
    rwa [spMap_comp ρ x, hy]

end GlobalTheory.LevelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOfPolarisedLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem obbuild_hf_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
  simp [hermForm, add_dotProduct]

theorem obbuild_hf_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem obbuild_hf_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm (r • a) c = r * hermForm Hm a c := by
  simp [hermForm, smul_dotProduct]

theorem obbuild_hf_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm a (r • c) = star r * hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

theorem obbuild_adj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im) (z z' : Fin g → ℂ) :
    hermForm Hm (F z) z' = hermForm Hm z (F' z') := by
  have hz : ∀ z : Fin g → ℂ, hermForm Hm 0 z = 0 ∧ hermForm Hm z 0 = 0 := fun z => by simp [hermForm]
  have hr : ∀ (r : ℝ) (z : Fin g → ℂ), r • z = (r : ℂ) • z := fun r z => by
    ext i; simp
  have h1 : ∀ a ∈ s, ∀ c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a ha c
    have hc : c ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact h a ha x hx
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_right, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_right, obbuild_hf_smul_right]; simp [hx]
  have h2 : ∀ a c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a c
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact h1 x hx c
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_left, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]; simp [hx]
  apply Complex.ext
  · have := h2 (Complex.I • z) z'
    rw [map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left] at this
    simpa using this
  · exact h2 z z'

theorem obbuild_ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  induction n with
  | zero => simp [(u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem obbuild_unitS {o : Type} [CommRing o] (em : o →+* ℂ) (u : oˣ) :
    unitS (spMap em) u = unitOn (Units.map em.toMonoidHom u) := by
  ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em)
  exact (congrArg (fun f => f.hom (u : o)) this).symm

theorem obbuild_unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n := by
  simp [unitOn]

theorem thetaObject_of_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro h1 h2 h3 h4 o _ g k J b em w w' La _ EF lam ac Q Hm hE ⟨hQ, hdisc, hspan, hH, hpos, him⟩ hac hw hadj hlam
  choose F hF using hac
  let Λ : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap
  let e : La ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective Q.toIntLinearMap hQ
  have he : ∀ a : Λ, Q (e.symm a) = a := fun a => congrArg Subtype.val (e.apply_symm_apply a)
  have hbij : Function.Bijective (LinearMap.BilinForm.congr e EF) := by
    have : (LinearMap.BilinForm.congr e EF : Λ → Λ →ₗ[ℤ] ℤ) = e.symm.dualMap ∘ EF ∘ e.symm := by
      funext a; ext c; simp
    rw [this]
    exact e.symm.dualMap.bijective.comp (hE.comp e.symm.bijective)
  obtain ⟨P, u, χ, hg, hΛ, hAH, -, -⟩ := principalTorus_algebraic g Λ Hm (LinearMap.BilinForm.congr e EF) hdisc
    hspan hH hpos (fun a c => by rw [← he a, ← he c, him]; simp) hbij
  subst hg
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ]; rfl
  have hhom := fun j => _root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice h1 h2 h3 h4 P P P.L P.L u u (F j) (fun z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, (hF j x).symm⟩)
  choose act hact using fun j => (hhom j).exists
  have hFF : F w + F w' = LinearMap.id := by
    apply LinearMap.restrictScalars_injective ℝ
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [hF, ← map_add (f := _), hw]
  have hmul : act w * act w' = 𝟙 P.A := by
    haveI := P.isAb.comm
    haveI := (hact w).1
    haveI := (hact w').1
    refine (_root_.GlobalTheory.existsUnique_isMonHom_of_map_lattice h1 h2 h3 h4 P P P.L P.L u u LinearMap.id (fun z hz => hz)).unique ⟨?_, fun z => ?_⟩
      ⟨inferInstance, fun z => by simp⟩
    · rw [Hom.mul_def]; infer_instance
    · rw [MonObj.comp_mul, ← (hact w).2, ← (hact w').2, ← u.ex_add, ← LinearMap.add_apply, hFF]
  have hadjH : ∀ z z', hermForm Hm (F w z) z' = hermForm Hm z (F w' z') := by
    refine obbuild_adj Hm _ hspan _ _ ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hF, hF, him, him, hadj]
  have hiso := (_root_.GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm h1 h2 h3 h4 P u Hm χ _ _ _ _ hAH (hact w).1 (hact w').1 (hact w).2 (hact w').2).2 hadjH
  obtain ⟨m1, m2, m3, m4, m5, -, m7, m8⟩ := _root_.GlobalTheory.PrimNormPol.normalised_polarisation h1 h3 ℂ P _ _ (hact w).1 (hact w').1 hmul hiso _ rfl
  obtain ⟨Ef, hEf, -⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties h1 h2 h3 h4 P u Hm χ hAH
  obtain ⟨u₁, χ₁, hex, hΛ₁, hAH₁, hχ₁⟩ := _root_.GlobalTheory.PulledBiextFrame.exists_appellHumbert_frame h1 h2 h3 h4 P u Hm χ Ef (act w) (F w) (F w') hAH hEf
    (hact w).2 hFF hadjH
  let P₁ : Out.PolAV (Sp ℂ) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
      isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5 }
  obtain ⟨Ef₁, hEf₁, -, -, -, -, -, -, hweil⟩ := _root_.GlobalTheory.AnyAppellHumbert.isAH_properties h1 h2 h3 h4 P₁ u₁ Hm χ₁ hAH₁
  have hmem₁ : ∀ z, z ∈ u₁.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ₁]; exact hmem z
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  let pt : Fin (2 * P.g) → (Out.baseOver (Sp ℂ) ⟶ P.A) := fun i => u₁.ex ((k : ℂ)⁻¹ • Q (lam i))
  have htor : ∀ i, pt i ^ k = 1 := fun i => by
    have := obbuild_ex_pow u₁ ((k : ℂ)⁻¹ • Q (lam i)) k
    rw [smul_inv_smul₀ hk, (u₁.ker _).2 ((hmem₁ _).2 ⟨_, rfl⟩)] at this
    exact this
  have hpair : ∀ i j, Out.WeilIs P.A (cubeLB P.A ![𝟙 P.A, act w] P.L) k (pt i) (pt j)
      (unitOn (Units.map em.toMonoidHom b.ζ) ^ Out.stdSymp P.g i j) := fun i j => by
    rw [← obbuild_unitOn_zpow]
    refine hweil k ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩ _ hk0 ?_
    have h5 := hEf₁ ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him (lam i) (lam j), Int.cast_inj] at h5
    rw [h5, hlam]
    simp
  have hb := _root_.GlobalTheory.symplectic_system_torsion_basis h1 ℂ P₁ k (Units.map em.toMonoidHom b.ζ) pt hk
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em)) htor hpair
  refine ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
            isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5, pt := pt, torsion := htor, bij := hb,
            pairing := fun i j => by rw [obbuild_unitS]; exact hpair i j,
            act := act, hom := fun j => (hact j).1 }, ⟨hmul, m8, m7⟩, u₁, χ₁, hAH₁, hmem₁, ?_, fun _ => rfl, ?_⟩
  · intro x l hl
    rw [hχ₁ l ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩ hl.symm (by rw [hl, hF])]
    have h5 := hEf ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him x (ac w x), Int.cast_inj] at h5
    rw [h5]
  · intro j
    refine ⟨F j, hF j, fun z => ?_⟩
    have := (hact j).2 z
    rw [← hex] at this
    exact this

end GlobalTheory
end

