module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GrpObjDescendsFaithfullyFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.GrpDescent

variable {S S₀ : Scheme.{0}}

theorem grpObj_descends (f : S ⟶ S₀) [Flat f] [Surjective f] (A : Over S) [GrpObj A] (A₀ : Over S₀)
    (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over S₀) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀)
    (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left) (hπ : IsPullback π A.hom A₀.hom f)
    (h1 : π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π) (h2 : π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π)
    (he : η[A].left ≫ π = f ≫ e₀.left) (hm : μ[A].left ≫ π = π₂ ≫ m₀.left)
    (hi : (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left) :
    ∃ _ : GrpObj A₀, IsGrpPullback A A₀ f π := by

  have rmul : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' y' : T' ⟶ A} {x y : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → y'.left ≫ π = p ≫ y.left →
      (x' * y').left ≫ π = p ≫ (lift x y ≫ m₀).left := by
    intro T' T p x' y' x y hx hy
    have : (lift x' y').left ≫ π₂ = p ≫ (lift x y).left := by
      apply pullback.hom_ext
      · change ((lift x' y').left ≫ π₂) ≫ (fst A₀ A₀).left = (p ≫ (lift x y).left) ≫ (fst A₀ A₀).left
        rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, hx]
      · change ((lift x' y').left ≫ π₂) ≫ (snd A₀ A₀).left = (p ≫ (lift x y).left) ≫ (snd A₀ A₀).left
        rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, hy]
    rw [Hom.mul_def, Over.comp_left, Category.assoc, hm, ← Category.assoc, this, Over.comp_left, Category.assoc]
  have rone : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f →
      (1 : T' ⟶ A).left ≫ π = p ≫ (toUnit T ≫ e₀).left := by
    intro T' T p hp
    rw [Hom.one_def, Over.comp_left, Category.assoc, he, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (by rw [← hp]; exact Category.assoc _ _ _)
  have rinv : ∀ {T' : Over S} {T : Over S₀} (p : T'.left ⟶ T.left) {x' : T' ⟶ A} {x : T ⟶ A₀},
      x'.left ≫ π = p ≫ x.left → (x'⁻¹).left ≫ π = p ≫ (x ≫ i₀).left := by
    intro T' T p x' x hx
    rw [Hom.inv_def, Over.comp_left, Category.assoc, hi, ← Category.assoc, hx, Over.comp_left, Category.assoc]

  have cov : ∀ T : Over S₀, ∃ (T' : Over S) (p : T'.left ⟶ T.left), p ≫ T.hom = T'.hom ≫ f ∧
      (∀ a b : T ⟶ A₀, p ≫ a.left = p ≫ b.left → a = b) ∧
      ∀ x : T ⟶ A₀, ∃ x' : T' ⟶ A, x'.left ≫ π = p ≫ x.left := by
    intro T
    refine ⟨Over.mk (pullback.snd T.hom f), pullback.fst T.hom f, pullback.condition, fun a b h => ?_, fun x => ?_⟩
    · have : Epi (pullback.fst T.hom f) := Flat.epi_of_flat_of_surjective _
      ext1
      exact (cancel_epi (pullback.fst T.hom f)).1 h
    · refine ⟨Over.homMk (hπ.lift (pullback.fst T.hom f ≫ x.left) (pullback.snd T.hom f) ?_) ?_, ?_⟩
      · rw [Category.assoc, Over.w x, pullback.condition]
      · exact hπ.lift_snd _ _ _
      · exact hπ.lift_fst _ _ _
  have one_mul' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (toUnit T ≫ e₀) x ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rone p hp) hx, _root_.one_mul, hx]
  have mul_one' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (toUnit T ≫ e₀) ≫ m₀ = x := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rone p hp), _root_.mul_one, hx]
  have assoc' : ∀ {T : Over S₀} (x y z : T ⟶ A₀),
      lift (lift x y ≫ m₀) z ≫ m₀ = lift x (lift y z ≫ m₀) ≫ m₀ := by
    intro T x y z
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    obtain ⟨y', hy⟩ := hl y
    obtain ⟨z', hz⟩ := hl z
    apply hinj
    rw [← rmul p (rmul p hx hy) hz, ← rmul p hx (rmul p hy hz), _root_.mul_assoc]
  have linv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift (x ≫ i₀) x ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p (rinv p hx) hx, ← rone p hp, inv_mul_cancel]
  have rinv' : ∀ {T : Over S₀} (x : T ⟶ A₀), lift x (x ≫ i₀) ≫ m₀ = toUnit T ≫ e₀ := by
    intro T x
    obtain ⟨T', p, hp, hinj, hl⟩ := cov T
    obtain ⟨x', hx⟩ := hl x
    apply hinj
    rw [← rmul p hx (rinv p hx), ← rone p hp, mul_inv_cancel]
  let G : GrpObj A₀ :=
    { one := e₀
      mul := m₀
      one_mul := by
        rw [← one_mul' (λ_ A₀).hom]
        congr 1
      mul_one := by
        rw [← mul_one' (ρ_ A₀).hom]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · rw [whiskerLeft_fst, lift_fst, rightUnitor_hom]
        · rw [whiskerLeft_snd, lift_snd]
          congr 1
          exact toUnit_unique _ _
      mul_assoc := by
        have h := assoc' (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀)
        have a1 : m₀ ▷ A₀ = lift (lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ m₀)
            (snd (A₀ ⊗ A₀) A₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [whiskerRight_fst, lift_fst, ← comp_lift, lift_fst_snd, Category.comp_id]
          · rw [whiskerRight_snd, lift_snd]
        have a2 : (α_ A₀ A₀ A₀).hom ≫ A₀ ◁ m₀ = lift (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀)
            (lift (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) (snd (A₀ ⊗ A₀) A₀) ≫ m₀) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [Category.assoc, whiskerLeft_fst, lift_fst, associator_hom_fst]
          · rw [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc]
            congr 1
            apply CartesianMonoidalCategory.hom_ext
            · rw [Category.assoc, lift_fst, associator_hom_snd_fst]
            · rw [Category.assoc, lift_snd, associator_hom_snd_snd]
        rw [← Category.assoc, a2, a1, h]
      inv := i₀
      left_inv := by simpa only [Category.id_comp] using linv' (𝟙 A₀)
      right_inv := by simpa only [Category.id_comp] using rinv' (𝟙 A₀) }
  refine ⟨G, hπ, fun T x y x₀ y₀ hx hy => ?_⟩
  have := rmul (T' := T) (T := Over.mk (T.hom ≫ f)) (𝟙 T.left) (x' := x) (y' := y) (x := x₀) (y := y₀)
    (hx.symm.trans (Category.id_comp _).symm) (hy.symm.trans (Category.id_comp _).symm)
  exact (this.trans (Category.id_comp _)).symm

theorem grpObj_descends_faithfullyFlat : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp R₀)) [Flat A₀.hom] [IsSeparated A₀.hom] [QuasiCompact A₀.hom] (π : A.left ⟶ A₀.left) (e₀ : 𝟙_ (Over (Sp R₀)) ⟶ A₀) (m₀ : A₀ ⊗ A₀ ⟶ A₀) (i₀ : A₀ ⟶ A₀) (π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left), IsPullback π A.hom A₀.hom (spMap (algebraMap R₀ R)) → π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π → π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π → η[A].left ≫ π = spMap (algebraMap R₀ R) ≫ e₀.left → μ[A].left ≫ π = π₂ ≫ m₀.left → (GrpObj.inv : A ⟶ A).left ≫ π = π ≫ i₀.left → ∃ _ : GrpObj A₀, IsGrpPullback A A₀ (spMap (algebraMap R₀ R)) π := by
  intro R₀ R _ _ _ _ A _ A₀ _ _ _ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi
  have hff : (algebraMap R₀ R).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 ‹_›
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R₀ R))).2 hff
  exact grpObj_descends _ A A₀ π e₀ m₀ i₀ π₂ hπ h1 h2 he hm hi

end GlobalTheory.GrpDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

def comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) (c : Fin N → Γ(T, W)) (y : Y)
    (i : L.ι) : Y.presheaf.stalk y :=
  ∑ k, gs p₁ y W (c k) * gs p₂ y (L.U i) ((b k).f i)

def IndepOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ c : Fin N → Γ(T, W), (∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → comb b p₁ p₂ W c y i = 0) → c = 0

def SpanOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ σ : ∀ i : L.ι, Γ(Y, p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i),
    (∀ (y : Y) (i i' : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y _ (σ i) = (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val * gs (𝟙 Y) y _ (σ i')) →
    ∃ c : Fin N → Γ(T, W), ∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ W c y i

def BoxSpan (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) : Prop :=
  ∀ (K : Type) [Fintype K] (φ : K → (T ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim ε (fun _ => t)))),
    ∃ a : Fin N → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ k, sval (a k) (r ≫ p₁) z J * gs (r ≫ p₂) z (L.U (J (r ≫ p₂))) ((b k).f (J (r ≫ p₂)))

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [← gs_pull r f z U h, gs_eq f (r z) U h, gs_eq r z (f ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

def gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eq_gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = gsHom f y U h a := gs_eq f y U h a

theorem comb_comp {Z : Scheme.{0}} (b : Fin N → LB.Sec (pw L t)) (r : Z ⟶ Y) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (c : Fin N → Γ(T, W)) (z : Z) (i : L.ι) (h₁ : p₁ (r z) ∈ W) (h₂ : p₂ (r z) ∈ L.U i) :
    comb b (r ≫ p₁) (r ≫ p₂) W c z i = (r.stalkMap z).hom (comb b p₁ p₂ W c (r z) i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, gs_comp r p₁ z W h₁]
  exact congrArg _ (gs_comp r p₂ z (L.U i) h₂ _)

end GlobalTheory.RelBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsMaximalOfFinitePrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.GermInterp

theorem isMaximal_of_finite_primes {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) (Q : Ideal R) (hQ : Q.IsPrime) (hI : I ≤ Q) :
    Q.IsMaximal := by
  have hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro J ⟨hQJ, hJ⟩
    exact ⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩
  have hJac : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  have hinf : hT.toFinset.inf id ≤ Q := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact hJac.le
  obtain ⟨M, hM, hMQ⟩ := hQ.inf_le'.1 hinf
  rw [Set.Finite.mem_toFinset] at hM
  rw [show Q = M from le_antisymm hM.1 hMQ]
  exact hM.2

theorem eq_of_comap_map_le {R : Type*} [CommRing R] (I : Ideal R)
    (hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) (P : Ideal R) [hP : P.IsPrime] (hI : I ≤ P)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (M : Ideal R) (hM : M.IsMaximal)
    (h : (I.map (algebraMap R S)).comap (algebraMap R S) ≤ M) : M = P := by
  by_contra hne
  have hMP : ¬ M ≤ P := fun hle => hne (hM.eq_of_le hP.ne_top hle)
  obtain ⟨m, hmM, hmP⟩ := Set.not_subset.1 hMP
  have hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R) := by
    intro hdis
    obtain ⟨Q, hQ, hIQ, hQdis⟩ := Ideal.exists_le_prime_disjoint I _ hdis
    have hQM : Q ≤ M := by
      intro x hx
      by_contra hxM
      exact Set.disjoint_left.1 hQdis hx
        (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))
    have hmQ : m ∉ Q := fun hm =>
      Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))
    exact hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)
  obtain ⟨w, hwI, hwW⟩ := Set.not_disjoint_iff.1 hmeet
  obtain ⟨v, hv, u, hu, rfl⟩ := Submonoid.mem_sup.1 hwW
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hu
  have hunit : IsUnit (algebraMap R S (m ^ k)) :=
    IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)
  have hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
    rw [Ideal.mem_comap]
    have hw := Ideal.mem_map_of_mem (algebraMap R S) hwI
    rw [map_mul] at hw
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 hw
  exact hv (h hvmap)

theorem exists_sub_mem_map {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) {κ : Type*} [Finite κ] (P : κ → PrimeSpectrum R)
    (hinj : Function.Injective P) (hI : ∀ i, I ≤ (P i).asIdeal) (S : κ → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalization.AtPrime (S i) (P i).asIdeal] (a : ∀ i, S i) :
    ∃ r : R, ∀ i, algebraMap R (S i) r - a i ∈ I.map (algebraMap R (S i)) := by
  have hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal :=
    fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ
  let N : κ → Ideal R := fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))
  have key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal :=
    fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle
  have hcop : Pairwise fun i j => IsCoprime (N i) (N j) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have e1 := key i M hM (le_trans le_sup_left hle)
    have e2 := key j M hM (le_trans le_sup_right hle)
    exact hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))
  have hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i := by
    intro i
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)
    exact ⟨x, s, h⟩
  choose x s hxs using hfrac
  have hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i := by
    intro i
    have hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have e := key i M hM (le_trans le_sup_left hle)
      have hsM : (s i : R) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [e] at hsM
      exact (s i).2 hsM
    have h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)} := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine ⟨t, ?_⟩
    have e : (s i : R) * t - 1 = -y := by rw [← hyz]; ring
    rw [e]
    exact (N i).neg_mem hy
  choose t ht using hinv
  obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨r, fun i => ?_⟩
  have hri : r - x i * t i ∈ N i := by
    have e := congrFun hz i
    rw [Ideal.quotientInfToPiQuotient_mk'] at e
    exact Ideal.Quotient.eq.1 e
  have h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i)) := by
    rw [← map_sub]
    exact Ideal.mem_comap.1 hri
  have h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i)) := by
    rw [← hxs i]
    have hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i)) :=
      Ideal.mem_comap.1 (ht i)
    have hspec := IsLocalization.mk'_spec (S i) (x i) (s i)
    have e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) =
        IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1) := by
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap R (S i) (t i))) * hspec
    rw [e]
    exact Ideal.mul_mem_left _ _ hst
  convert Ideal.add_mem _ h1 h2 using 1
  ring

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (y : X) (hy : y ∈ V)
    (g : Γ(X, V)) : g ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↔ y ∉ X.basicOpen g := by
  have h1 : hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g ↔ y ∈ X.basicOpen g := by
    show hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen g ↔ _
    rw [hV.fromSpec_primeIdealOf]
  rw [hV.fromSpec_preimage_basicOpen] at h1
  constructor
  · intro hg hyb
    exact (h1.2 hyb) hg
  · intro hyb
    by_contra hg
    exact hyb (h1.1 hg)

theorem exists_germ_sub_mem : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by
  intro K _ X p V J f a hft hV hfin
  let I : Ideal Γ(X, V) := Ideal.span (Set.range f)
  let Z := {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}
  have : Finite Z := hfin.to_subtype
  let P : Z → PrimeSpectrum Γ(X, V) := fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩
  have hIP : ∀ k, I ≤ (P k).asIdeal := by
    intro k
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)
  have hinj : Function.Injective P := by
    intro k k' e
    apply Subtype.ext
    have e1 := hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩
    have e2 := hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩
    have e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩ := e
    rw [e3] at e1
    exact e1.symm.trans e2
  have hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite := by
    refine (Set.finite_range P).subset ?_
    intro Q hQ
    have hyV : hV.fromSpec Q ∈ V := hV.range_fromSpec.le ⟨Q, rfl⟩
    have hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)
    refine ⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩
    have hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal := by
      rw [hQeq]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi
  have : IsJacobsonRing Γ(Sp K, ⊤) :=
    isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom,
      RingEquiv.surjective _⟩
  have : IsJacobsonRing Γ(X, V) :=
    RingHom.FiniteType.isJacobsonRing
      (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))
  letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) :=
    fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩
  have loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal :=
    fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)
  refine ⟨r, fun y hy hz => ?_⟩
  let k : Z := ⟨y, hy, hz⟩
  have hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g := by
    intro g
    rw [gs_eq (𝟙 X) y V hy g]
    rfl
  have hk := hr k
  rw [Ideal.map_span, ← Set.range_comp] at hk
  have e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f := by
    funext i
    exact hgs (f i)
  rw [e, hgs r]
  exact hk

end GlobalTheory.GermInterp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isGrpPullback_of_fpqc (S S' S'' : Scheme.{0}) (a : S' ⟶ S) (π : S'' ⟶ S') (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (G'' : Over S'') [GrpObj G''] (φ : G''.left ⟶ G'.left) (ψ : G'.left ⟶ G.left)
    (hf : Flat π) (hs : Surjective π) (hq : QuasiCompact π) (h₁ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' π φ)
    (h₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G (π ≫ a) (φ ≫ ψ)) (w : ψ ≫ G.hom = G'.hom ≫ a) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G a ψ := by
  refine ⟨?_, ?_⟩
  · let c : G'.left ⟶ pullback G.hom a := pullback.lift ψ G'.hom w
    have hc₁ : c ≫ pullback.fst G.hom a = ψ := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd G.hom a = G'.hom := pullback.lift_snd _ _ _
    have hlow : IsPullback (φ ≫ c) G''.hom (pullback.snd G.hom a) π :=
      (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback G.hom a)
        (by rw [Category.assoc, hc₂, h₁.1.w])).1 (by rw [Category.assoc, hc₁]; exact h₂.1)
    have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (φ ≫ c) :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hlow.flip hs,
        MorphismProperty.of_isPullback (P := @Flat) hlow.flip hf⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) hlow.flip hq⟩
    have hsq : IsPullback (𝟙 G''.left) φ (φ ≫ c) c :=
      ((IsPullback.paste_vert_iff (h₁₁ := φ) (v₁₁ := 𝟙 _) (v₁₂ := c) hlow (by simp)).1
        (by rw [Category.id_comp, hc₂]; exact h₁.1)).flip
    have hc : IsIso c :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq hcov (inferInstanceAs (IsIso (𝟙 G''.left)))
    exact IsPullback.of_iso (IsPullback.of_hasPullback G.hom a) (asIso c).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [IsIso.eq_inv_comp, hc₁]) (by simp [IsIso.eq_inv_comp, hc₂])
      (by simp) (by simp)
  · intro T x y x₀ y₀ hx hy
    haveI := hf
    haveI := hs
    let p : pullback T.hom π ⟶ T.left := pullback.fst T.hom π
    haveI : Epi p := Flat.epi_of_flat_of_surjective _
    let T'' : Over S'' := Over.mk (pullback.snd T.hom π)
    let q : Over.mk (T''.hom ≫ π) ⟶ T := Over.homMk p (by simp [p, T'', pullback.condition])
    let q₀ : Over.mk (T''.hom ≫ π ≫ a) ⟶ Over.mk (T.hom ≫ a) :=
      Over.homMk p (by simp [p, T'', pullback.condition_assoc])
    let x'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ x.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    let y'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ y.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    have hx'' : x''.left ≫ φ = p ≫ x.left := by simp [x'']
    have hy'' : y''.left ≫ φ = p ≫ y.left := by simp [y'']
    have k₁ := h₁.2 T'' x'' y'' (q ≫ x) (q ≫ y) (by simp [q, hx'']) (by simp [q, hy''])
    have k₂ := h₂.2 T'' x'' y'' (q₀ ≫ x₀) (q₀ ≫ y₀)
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hx, reassoc_of% hx''])
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hy, reassoc_of% hy''])
    rw [← cancel_epi p]
    calc p ≫ (x₀ * y₀).left = (q₀ ≫ (x₀ * y₀)).left := by simp [q₀]
      _ = ((q₀ ≫ x₀) * (q₀ ≫ y₀)).left := by rw [comp_mul]
      _ = (x'' * y'').left ≫ φ ≫ ψ := k₂
      _ = ((q ≫ x) * (q ≫ y)).left ≫ ψ := by rw [k₁, Category.assoc]
      _ = (q ≫ (x * y)).left ≫ ψ := by rw [comp_mul]
      _ = p ≫ (x * y).left ≫ ψ := by simp [q]

end GlobalTheory
end

