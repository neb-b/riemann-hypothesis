module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SectionsSeparatePointsAndTangents
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversally
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.GenericZeros
open EtBaseChange


open scoped IntermediateField.algebraAdjoinAdjoin in
set_option synthInstance.maxHeartbeats 200000 in
theorem trdeg_adjoin_range_le {k K B : Type} [Field k] [Field K] [Algebra k K] [CommRing B] [Algebra k B]
    (ψ : B →ₐ[k] K) : Algebra.trdeg k (IntermediateField.adjoin k (Set.range ψ)) ≤ Algebra.trdeg k B := by
  rw [trdeg_eq_of_isAlgebraic_top k (Algebra.adjoin k (Set.range ψ)) (IntermediateField.adjoin k (Set.range ψ))]
  refine trdeg_le_of_surjective (ψ.codRestrict _ fun b => Algebra.subset_adjoin ⟨b, rfl⟩) ?_
  rintro ⟨y, hy⟩
  have hle : Algebra.adjoin k (Set.range ψ) ≤ ψ.range := Algebra.adjoin_le fun _ h => h
  obtain ⟨b, hb⟩ := hle hy
  exact ⟨b, Subtype.ext hb⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_field_of_definition {k K : Type} [Field k] [Field K] [Algebra k K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Sp k) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (p : Sp K ⟶ X)
    (hp : p ≫ f = spMap (algebraMap k K)) :
    ∃ F : IntermediateField k K, Algebra.trdeg k F ≤ g ∧ ∃ q : Sp F ⟶ X,
      q ≫ f = spMap (algebraMap k F) ∧ spMap (algebraMap F K) ≫ q = p := by
  obtain ⟨R, j, hj, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := p (IsLocalRing.closedPoint K)) (U := ⊤) trivial
  have hr : Set.range p ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact hmem
  let ψ₀ : R ⟶ CommRingCat.of K := Spec.preimage (IsOpenImmersion.lift j p hr)
  have h₀ : Spec.map ψ₀ ≫ j = p := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  let a : CommRingCat.of k ⟶ R := Spec.preimage (j ≫ f)
  have ha : j ≫ f = Spec.map a := (Spec.map_preimage _).symm
  let _ : Algebra k R := a.hom.toAlgebra
  have hc : a ≫ ψ₀ = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← ha, ← Category.assoc, h₀, hp]
  let ψ : R →ₐ[k] K := { ψ₀.hom with commutes' := fun r => congrArg (fun q => q.hom r) hc }
  have : Nontrivial R := ψ₀.hom.domain_nontrivial
  have htr : Algebra.trdeg k R = g := trdeg_eq_of_smoothOfRelativeDimension k X f g hf R j hj ha
  let F := IntermediateField.adjoin k (Set.range ψ)
  let ψ' : R →+* F := ψ₀.hom.codRestrict F fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩
  refine ⟨F, htr ▸ trdeg_adjoin_range_le ψ, spMap ψ' ≫ j, ?_, ?_⟩
  · have e : ψ'.comp a.hom = algebraMap k F := RingHom.ext fun r => Subtype.ext (ψ.commutes r)
    rw [Category.assoc, ← e, ← spMap_comp]
    exact congrArg (spMap ψ' ≫ ·) ha
  · rw [← Category.assoc, spMap_comp]
    exact h₀

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (f : X ⟶ Sp R) (p : Sp T ⟶ X) (a : R →+* T)
    (hp : p ≫ f = spMap a) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : R) : valT p U (cst f U c) = a c := by
  have h0 : valT p U (cst f U c) =
      valT p U ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE p f (U := ⊤) le_top h _).trans ?_)
  rw [hp, ← Category.comp_id (spMap a), valT_spMap a (𝟙 (Sp R)) (U := ⊤) le_top, valT_eq _ _ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  simp

theorem exists_translate {k F K : Type} [CommRing k] [CommRing F] [CommRing K] (a : k →+* F) (e : F →+* K)
    {G : Over (Sp k)} [GrpObj G] {G' : Over (Sp K)} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (spMap (e.comp a)) φ) (E : DualNumber k →+* DualNumber K)
    (h₁ : ∀ r, E (algebraMap k _ r) = algebraMap K _ (e (a r))) (h₂ : E DualNumber.eps = DualNumber.eps)
    (z' : 𝟙_ (Over (Sp K)) ⟶ G') (q : Sp F ⟶ G.left) (hq : q ≫ G.hom = spMap a) (hz : spMap e ≫ q = z'.left ≫ φ)
    (v : epsR k ⟶ G) (v' : epsR K ⟶ G') (hv : v'.left ≫ φ = spMap E ≫ v.left) :
    ∃ r : Sp (DualNumber F) ⟶ G.left,
      ((toUnit (epsR K) ≫ z') * v').left ≫ φ = spMap (Chart.dualMapR e) ≫ r := by
  have hE : (Chart.dualMapR e).comp (Chart.dualMapR a) = E := by
    refine RingHom.ext fun t => ?_
    have : t = algebraMap k _ t.fst + algebraMap k _ t.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    conv_rhs => rw [this, map_add (f := _), map_mul, h₁, h₁, h₂]
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have c₁ : (Chart.dualMapR e).comp (algebraMap F (DualNumber F)) = (algebraMap K (DualNumber K)).comp e := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have c₂ : (Chart.dualMapR a).comp (algebraMap k (DualNumber k)) = (algebraMap F (DualNumber F)).comp a := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have s₁ : spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap e := by rw [spMap_comp, spMap_comp, c₁]
  have s₂ : spMap (Chart.dualMapR a) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap F (DualNumber F)) ≫ spMap a := by rw [spMap_comp, spMap_comp, c₂]
  let T : Over (Sp k) := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap a)
  let qT : T ⟶ G := Over.homMk (spMap (algebraMap F (DualNumber F)) ≫ q)
    ((Category.assoc _ _ _).trans (congrArg (spMap (algebraMap F (DualNumber F)) ≫ ·) hq))
  have hvw : v.left ≫ G.hom = spMap (algebraMap k (DualNumber k)) := Over.w v
  let vT : T ⟶ G := Over.homMk (spMap (Chart.dualMapR a) ≫ v.left)
    ((Category.assoc _ _ _).trans ((congrArg (spMap (Chart.dualMapR a) ≫ ·) hvw).trans s₂))
  have hD : spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) ≫ spMap a =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (e.comp a) := by
    rw [← Category.assoc, s₁, Category.assoc, spMap_comp a e]
  let D : Over.mk ((epsR K).hom ≫ spMap (e.comp a)) ⟶ T := Over.homMk (spMap (Chart.dualMapR e)) hD
  have e₁ : (D ≫ qT).left = (toUnit (epsR K) ≫ z').left ≫ φ := by
    show spMap (Chart.dualMapR e) ≫ spMap (algebraMap F (DualNumber F)) ≫ q =
      (spMap (algebraMap K (DualNumber K)) ≫ z'.left) ≫ φ
    rw [← Category.assoc, s₁, Category.assoc, hz]
    exact (Category.assoc _ _ _).symm
  have e₂ : (D ≫ vT).left = v'.left ≫ φ := by
    refine Eq.trans ?_ hv.symm
    show spMap (Chart.dualMapR e) ≫ spMap (Chart.dualMapR a) ≫ v.left = _
    rw [← Category.assoc, spMap_comp, hE]
  refine ⟨(qT * vT).left, ?_⟩
  rw [← h.2 (epsR K) _ _ (D ≫ qT) (D ≫ vT) e₁ e₂, ← MonObj.comp_mul]
  rfl

theorem sum_valT_via {k K T : Type} [CommRing k] [CommRing K] [CommRing T] {x : KeyIn k} {x' : KeyIn K}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} {n N : ℕ} {b : Fin N → RR x n}
    {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j)) (p : Sp T ⟶ x'.P.A.left) (a : K →+* T)
    (hp : p ≫ x'.P.A.hom = spMap a) (c : x.P.L.ι) (c' : x'.P.L.ι) (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c)
    (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') (t : RR x' n) (m : Fin N → K) (ht : Coords x' b' m t.f) :
    ∑ j, a (m j) * valT (p ≫ φ) (x.P.L.U c) ((b j).f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ n *
        valT p (x'.P.L.U c') (t.f c') := by
  have e : valT p (x'.P.L.U c') (t.f c') = ∑ j, a (m j) * valT p (x'.P.L.U c') ((b' j).f c') := by
    refine (congrArg (valT p (x'.P.L.U c')) (ht c')).trans ((valT_eq p _ h' _).trans ((map_sum _ _ _).trans ?_))
    refine Finset.sum_congr rfl fun j _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (valT_eq p _ h' _).symm)
    exact (valT_eq p _ h' _).symm.trans (valT_cst _ p a hp _ h' _)
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [valT_via (hb j) p c c' h h', mul_left_comm]

theorem exists_jets {k K : Type} [Field k] [Field K] [Algebra k K] {x : KeyIn k} {x' : KeyIn K}
    {φ : x'.P.A.left ⟶ x.P.A.left} {w : LB.Iso x'.P.L (x.P.L.pull φ)} (H : KeyVia x' x (algebraMap k K) φ w)
    {n N : ℕ} {b : Fin N → RR x n} {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    (z : Pt x') (c' : x'.P.L.ι) (h' : ⊤ ≤ z.left ⁻¹ᵁ x'.P.L.U c') :
    ∃ (F : IntermediateField k K) (e : Fin N → K) (D : Fin x'.P.g → Fin N → K) (u : K), u ≠ 0 ∧
      Algebra.trdeg k F ≤ x'.P.g ∧ (∀ j, e j ∈ F) ∧ (∀ a j, D a j ∈ F) ∧
      ∀ (t : RR x' n) (m : Fin N → K), Coords x' b' m t.f →
        ∑ j, m j * e j = u * valT (T := K) z.left (x'.P.L.U c') (t.f c') ∧
        (valT (T := K) z.left (x'.P.L.U c') (t.f c') = 0 → ∀ a, ∑ j, m j * D a j = u * TrivSqZeroExt.snd
          (valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * x'.v a).left (x'.P.L.U c') (t.f c'))) := by
  obtain ⟨-, hg, E, hp, -, -, -, hE₁, hE₂, hv⟩ := H
  have : IsIntegral x.P.A.left := isIntegral_left_of_isAbelianScheme_field x.P.A x.P.isAb
  let z₀ : Sp K ⟶ x'.P.A.left := z.left
  have hz : z₀ ≫ x'.P.A.hom = 𝟙 (Sp K) := Over.w z
  have hz' : z₀ ≫ x'.P.A.hom = spMap (RingHom.id K) := hz.trans (Spec.map_id _).symm
  obtain ⟨F, hF, q, hq, hzq⟩ := exists_field_of_definition x.P.A.hom x.P.g x.P.smoothDim (z₀ ≫ φ) (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, hz, Category.id_comp])
  obtain ⟨c, hc⟩ := exists_chart x.P.isLB (q (IsLocalRing.closedPoint F))
  have hqc : ⊤ ≤ q ⁻¹ᵁ x.P.L.U c := fun p _ => by
    obtain rfl : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    exact hc
  have hφ : ⊤ ≤ (z₀ ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [← hzq]
    exact hqc (show spMap (algebraMap F K) p ∈ ⊤ from trivial)
  have hW := le_inf_pull (T := K) z₀ c c' hφ h'
  let p : Fin x'.P.g → (Sp (DualNumber K) ⟶ x'.P.A.left) := fun a => ((toUnit (epsR K) ≫ z) * x'.v a).left
  have hpw : ∀ a, p a ≫ x'.P.A.hom = spMap (algebraMap K (DualNumber K)) := fun a =>
    Over.w ((toUnit (epsR K) ≫ z) * x'.v a)
  have l₂ : ∀ a, ⊤ ≤ p a ⁻¹ᵁ x'.P.L.U c' := fun a => translate_le z (x'.v a) (x'.basis.1 _) h'
  have l₃ : ∀ a, ⊤ ≤ (p a ≫ φ) ⁻¹ᵁ x.P.L.U c := fun a =>
    translate_le z (x'.v a) (x'.basis.1 _) (U := φ ⁻¹ᵁ x.P.L.U c) hφ
  let u := valT (T := K) z₀ ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val
  have hu : IsUnit u := by
    have := (w.s (fun _ => c, c')).isUnit.map (valH (T := K) z₀ _ hW)
    exact (congrArg IsUnit (valT_eq (T := K) z₀ _ hW _)).mpr this
  refine ⟨F, fun j => valT (z₀ ≫ φ) (x.P.L.U c) ((b j).f c),
    fun a j => (valT (p a ≫ φ) (x.P.L.U c) ((b j).f c)).snd, u ^ n, pow_ne_zero _ hu.ne_zero, hg ▸ hF,
    fun j => ?_, fun a j => ?_, fun t m ht => ⟨?_, fun h0 a => ?_⟩⟩
  · show valT (z₀ ≫ φ) _ _ ∈ F
    rw [← hzq]
    exact (congrArg (· ∈ F) (valT_spMap _ q hqc _)).mpr (Subtype.property _)
  · have hp' : IsGrpPullback x'.P.A x.P.A (spMap ((algebraMap F K).comp (algebraMap k F))) φ := by
      rw [← IsScalarTower.algebraMap_eq]; exact hp
    obtain ⟨r, hr⟩ := exists_translate (algebraMap k F) (algebraMap F K) hp' E hE₁ hE₂ z q hq hzq _ _ (hv a)
    have hr' : p a ≫ φ = spMap (Chart.dualMapR (algebraMap F K)) ≫ r := hr
    have hrc : ⊤ ≤ r ⁻¹ᵁ x.P.L.U c := fun y _ => by
      have h₁ := l₃ a (show IsLocalRing.closedPoint (DualNumber K) ∈ ⊤ from trivial)
      rw [hr'] at h₁
      have hsub : ∀ y y' : Sp (DualNumber F), y = y' := fun y y' => by
        obtain ⟨y, rfl⟩ := fst_surjective F y
        obtain ⟨y', rfl⟩ := fst_surjective F y'
        rw [Subsingleton.elim y y']
      rw [hsub y (spMap (Chart.dualMapR (algebraMap F K)) (IsLocalRing.closedPoint (DualNumber K)))]
      exact h₁
    show (valT (p a ≫ φ) _ _).snd ∈ F
    rw [hr']
    refine (congrArg (fun y : DualNumber K => y.snd ∈ F) (valT_spMap _ r hrc _)).mpr ?_
    simp [Chart.dualMapR]
  · exact sum_valT_via hb z₀ (RingHom.id K) hz' c c' hφ h' t m ht
  · have e := congrArg TrivSqZeroExt.snd (sum_valT_via hb (p a) _ (hpw a) c c' (l₃ a) (l₂ a) t m ht)
    rw [snd_pow_mul _ _ _ ((fst_valT_translate z (x'.v a) (x'.basis.1 _) h' _).trans h0)] at e
    refine Eq.trans ?_ (e.trans (congrArg (· ^ n * _) (fst_valT_translate z (x'.v a) (x'.basis.1 _) hW _)))
    rw [TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_etZ_of_algebraicIndependent : Out.Laws → ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s : Fin x'.P.g → RR x' n), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k T → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt x') (ch : Fin d → x'.P.L.ι), EtZ x' s z ch := by
  intro hL k K _ _ _ _ x x' φ w n b b' T s hn H hb hb' hT hs
  have hB : IsBasis x' b' := (GlobalTheory.KeyBasis.main hL k x n (by omega)).2 b hb K _ x' φ w b' H hb'
  refine GlobalTheory.KeyKa.exists_etZ_of_jac_ne_zero K x' n s fun z c hc h0 => ?_
  obtain ⟨F, e, D, u, hu, hF, he, hD, hval⟩ := exists_jets H hb' z c hc
  have hdet : ∀ (t : Fin x'.P.g → RR x' n) (m : Fin x'.P.g → Fin (n ^ x.P.g) → K),
      (∀ i, Coords x' b' (m i) (t i).f) → (∀ i, valT (T := K) z.left (x'.P.L.U c) ((t i).f c) = 0) →
      (∀ i, ∑ j, m i j * e j = 0) ∧
        (Matrix.of fun i a => ∑ j, m i j * D a j).det = u ^ Fintype.card (Fin x'.P.g) * jac x' t z c := by
    intro t m hm ht
    refine ⟨fun i => by rw [(hval _ _ (hm i)).1, ht i, mul_zero], Eq.trans ?_ (Matrix.det_smul _ _)⟩
    congr 1
    ext i a
    exact (hval _ _ (hm i)).2 (ht i) a
  obtain ⟨⟨s₀, hs₀⟩, t, ht, hj⟩ := (GlobalTheory.KeyKa.sections_separate_points_and_tangents hL K x' n hn).1 z c hc
  choose m hm _ using hB
  have h₁ := hdet s (fun i j => T (i, j)) hs h0
  have h₂ := hdet t (fun i => m (t i)) (fun i => hm _) ht
  have h₃ := GlobalTheory.det_ne_zero_of_generic_linear_forms_vanish k K F _ _ T e D hT hF he hD ?_
    ⟨_, h₂.1, h₂.2 ▸ mul_ne_zero (pow_ne_zero _ hu) hj⟩ h₁.1
  · exact right_ne_zero_of_mul (h₁.2 ▸ h₃)
  · by_contra hne
    push Not at hne
    have := (hval _ _ (hm s₀)).1
    simp only [hne, mul_zero, Finset.sum_const_zero] at this
    exact mul_ne_zero hu hs₀ this.symm

end GlobalTheory.KeyKa.GenericZeros
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyViaIsPullback
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.KeyKa

namespace GlobalTheory.KeyLine

section Via

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gs_unit_pow {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) (n : ℕ) :
    gs r z U (a.val ^ n) = (gm r z U a).val ^ n := by
  rw [← gs_unit r z U h, gs_eq r z U h, gs_eq r z U h, map_pow, map_pow]

theorem via_iff_stalk (w : LB.Iso L' (L.pull F)) (l : ℕ) (a' : ∀ i, Γ(X', L'.U i)) (a : ∀ j, Γ(X, L.U j)) :
    KeyVia.Via w l a' a ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (a j) = (gw w r z j k).val ^ l * gs r z _ (a' k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit_pow _ z _ hy _ l)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit_pow _ y _ hy _ l).symm

variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))} {l : ℕ}
  {a : ∀ j, Γ(X, L.U j)} {a' : ∀ i, Γ(X', L'.U i)} {a'' : ∀ i, Γ(X'', L''.U i)}

theorem via_comp (T : Tri w w' w'') (hL' : L'.IsLB) (h : KeyVia.Via w l a' a) (h' : KeyVia.Via w' l a'' a') :
    KeyVia.Via w'' l a'' a := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z j k hj hk => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' (q z))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h' Z q z i k hi hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, e', Units.val_mul, mul_pow, _root_.mul_assoc]

theorem via_cancel (T : Tri w w' w'') (hL : L.IsLB) (h : KeyVia.Via w l a' a) (h'' : KeyVia.Via w'' l a'' a) :
    KeyVia.Via w' l a'' a' := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z i k hi hk => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (F' (q z)))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h'' Z q z j k hj hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, Units.val_mul, mul_pow, _root_.mul_assoc] at e'
  exact ((Units.isUnit _).pow l).mul_left_cancel e'

end Via

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'} {x'' : KeyIn R''}
  {f : R →+* R'} {f' : R' →+* R''}

theorem keyVia_g {φ w} (h : KeyVia x' x f φ w) : x'.P.g = x.P.g := by
  obtain ⟨_, hg, _⟩ := h
  exact hg

theorem keyVia_isPullback {φ w} (h : KeyVia x' x f φ w) : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
  obtain ⟨_, _, _, h, _⟩ := h
  exact h.1

theorem keyVia_trans {φ w φ' w'} (H : KeyVia x' x f φ w) (H' : KeyVia x'' x' f' φ' w') :
    ∃ w'', KeyVia x'' x (f'.comp f) (φ' ≫ φ) w'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x' φ' w' s'' s' → SecVia x'' x (φ' ≫ φ) w'' s'' s := by
  obtain ⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' h h' => via_comp (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x'.P.isLB h h'⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem keyVia_cancel {φ w φ'' w''} (H : KeyVia x' x f φ w) (H'' : KeyVia x'' x (f'.comp f) φ'' w'') :
    ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ φ' ≫ φ = φ'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s → SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := H''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩, rfl,
    fun l s s' s'' h h'' => via_cancel (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x.P.isLB h h''⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueMemValuationSubring
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGenInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem value_mem_valuationSubring (κ : Rule) (hU : UnitSp κ) (S K : Type) [CommRing S] [Field K] [CharZero K] [Algebra S K]
    (y : KeyIn S) (x : KeyIn K) (h : KeyPB x y (algebraMap S K)) (V : ValuationSubring K) (hV : IsDiscreteValuationRing V)
    (hS : ∀ s : S, algebraMap S K s ∈ V) : (κ K x : K) ∈ V ∧ (κ K x : K)⁻¹ ∈ V := by
  let j : S →+* V := (algebraMap S K).codRestrict V.toSubring hS
  obtain ⟨yV, hyV⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j
  have hc : (algebraMap V K).comp j = algebraMap S K := RingHom.ext fun _ => rfl
  have hx : KeyPB x yV (algebraMap V K) :=
    GlobalTheory.KeyCancel.keyPB_cancel S V K y yV x j (algebraMap V K) hyV (by rw [hc]; exact h)
  obtain ⟨u, hu, -⟩ := hU V K yV x hx
  refine ⟨?_, ?_⟩
  · rw [hu]; exact (u : V).2
  · have : (κ K x : K)⁻¹ = algebraMap V K (u⁻¹ : Vˣ) := by
      rw [hu]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact ((u⁻¹ : Vˣ) : V).2

theorem isIntegral_value : ∀ κ : Rule, UnitSp κ → ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [CharZero K] [Algebra S K] [IsFractionRing S K] (y : KeyIn S) (x : KeyIn K), KeyPB x y (algebraMap S K) →
    IsIntegral S (κ K x : K) ∧ IsIntegral S ((κ K x : K)⁻¹) := by
  intro κ hU S K _ _ _ _ _ _ _ y x h
  exact ⟨GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).1,
    GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).2⟩

end GlobalTheory.KeyGenInt
end
end

