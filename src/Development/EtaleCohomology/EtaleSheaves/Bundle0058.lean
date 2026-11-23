module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.EtaleCohomology.EtaleSheaves.Bundle0051
public import Development.EtaleCohomology.EtaleSheaves.Bundle0049
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0052
public import Development.EtaleCohomology.EtaleSheaves.Bundle0045

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafVanBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafVanBPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev bpl (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) (m : ℤ) :=
  rpl q i (prB ι U) (pullback.fst (t ≫ U.hom) ι)
    (pullback.map (t ≫ U.hom) ι U.hom ι t (𝟙 W) (𝟙 B) (by simp) (by simp)) t (pullback.lift_fst _ _ _).symm m

def LeafVanBStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (m : ℤ)
  (c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ U.left), SH A → IsUnit (q : A) → bpl q i ι U t m c = 0) →
  Cov U (fun _ a => rB q i ι a m c = 0)

def LeafRelVanOfH : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  Subsingleton (H R E F n) → Function.Surjective (pull R f F (n - 1)) → Subsingleton (Hrel R f F n)

theorem relVanOfH : LeafRelVanOfH := by
  intro R _ F U E f n hE hs
  suffices h : ∀ y : Hrel R f F n, y = 0 from ⟨fun y₁ y₂ => by rw [h y₁, h y₂]⟩
  intro y
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  set φ := (chains R).map f with hφ
  let a : Cocycle ((chains R).obj E) (res R F) n := zcomp (Cocycle.ofHom (mappingCone.inr φ)) z (zero_add n)
  have ha : CohomologyClass.mk a = 0 := hE.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha
  obtain ⟨α, hα⟩ := ha
  let b : Cochain ((chains R).obj U) (res R F) (n - 1) := (mappingCone.inl φ).comp z.1 (by omega)
  have hz : z.1 = mappingCone.descCochain φ b a.1 (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [b, a, zcomp, mappingCone.inl_descCochain, mappingCone.inr_descCochain]
  have h0 : δ n (n + 1) z.1 = 0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, mappingCone.δ_descCochain _ _ _ _ (n + 1) rfl] at h0
  have h1 := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) h0
  simp only [Cochain.comp_add, Cochain.comp_zero, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at h1
  have hδα : δ (n - 1) n α = a.1 := hα
  let b' : Cochain ((chains R).obj U) (res R F) (n - 1) :=
    b - n.negOnePow • (Cochain.ofHom φ).comp α (zero_add _)
  have hb' : δ (n - 1) n b' = 0 := by
    have e1 : δ (n - 1) n b = -((n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) := eq_neg_of_add_eq_zero_left h1
    simp only [b', δ_sub, δ_units_smul, e1, Int.negOnePow_succ]
    simp
    rw [hδα, sub_self]
  obtain ⟨g, hg⟩ := hs (CohomologyClass.mk (Cocycle.mk b' n (by omega) hb'))
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective g
  have hg' : CohomologyClass.mk (Cocycle.mk b' n (by omega) hb' - zcomp (Cocycle.ofHom φ) γ (zero_add _)) = 0 := by
    rw [CohomologyClass.mk_sub, ← hg]; exact sub_eq_zero.mpr rfl
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 2) (by omega)] at hg'
  obtain ⟨ε, hε⟩ := hg'
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨mappingCone.descCochain φ ε (α + n.negOnePow • γ.1) (by omega), ?_⟩
  have hε' : δ (n - 2) (n - 1) ε = b' - (Cochain.ofHom φ).comp γ.1 (zero_add _) := hε
  have hX : δ (n - 2) (n - 1) ε + n.negOnePow • (Cochain.ofHom φ).comp (α + n.negOnePow • γ.1) (zero_add _) = b := by
    rw [hε']
    simp only [b', Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    abel
  have hY : δ (n - 1) n (α + n.negOnePow • γ.1) = a.1 := by
    rw [δ_add, δ_units_smul, hδα, Cocycle.δ_eq_zero γ n, smul_zero, add_zero]
  rw [mappingCone.δ_descCochain _ _ _ _ n (by omega), hX, hY, hz]
  rfl

def LeafClosedSH : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  (∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)) ∧
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

def LeafClosedSHPos : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  ∀ n : ℤ, 0 < n → Subsingleton (H (ZMod q) (sch.obj W') (tw q i) n)

def LeafClosedSH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A →
  IsUnit (q : A) → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  Function.Surjective (pull (ZMod q) (sch.map ι') (tw q i) 0)

theorem closedSH_of (h1 : LeafClosedSHPos) (h2 : LeafClosedSH0) : LeafClosedSH :=
  fun hy q _ i A _ _ hA hq _ ι' _ => ⟨h1 hy q i A hA hq ι', h2 hy q i A hA hq ι'⟩

theorem heightFunctionalStatement_of_pairingProperties (hy : Hyps) : B2 := hy.2.2.2.2.2.2.2.2.2.2.2.1

theorem vanBPt (hC : LeafClosedSH) (hy : Hyps) (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A]
    [IsLocalRing A] (hA : SH A) (hq : IsUnit (q : A)) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] (m : ℤ)
    (hm : 0 < m) : Subsingleton (Hrel (ZMod q) (sch.map ι') (tw q i) m) := by
  obtain ⟨hW, hs⟩ := hC hy q i A hA hq ι'
  refine relVanOfH (ZMod q) (tw q i) (sch.map ι') m (heightFunctionalStatement_of_pairingProperties hy (ZMod q) A hA (tw q i) m hm) ?_
  rcases eq_or_lt_of_le (show (1 : ℤ) ≤ m by omega) with h | h
  · subst h; simpa using hs
  · have := hW (m - 1) (by omega)
    intro y; exact ⟨0, Subsingleton.elim _ _⟩

theorem LeafVanB_of (hS : LeafVanBStalk) (hP : LeafClosedSHPos) (h0 : LeafClosedSH0) : LeafVanB := by
  have hC := closedSH_of hP h0
  intro hy q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 h1 h2 h3 hsh U m hm c
  exact hS hy q k hq i s ι U m c (fun A _ _ t hA hqA =>
    (vanBPt hC hy q i A hA hqA (pullback.fst (t ≫ U.hom) ι) m hm).elim _ _)

end LateralTheory.E.LeafVanBPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LiftPf
section
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut

namespace LateralTheory.E.LiftPf

theorem orthF {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfo : ∀ l m, l ≠ m → ε l * ε m = 0) {e e' : A} (he : e ∈ P.1) (he' : e' ∈ P.1) {l m : Fin n}
    (hne : (e, l) ≠ (e', m)) : e * ε l * (e' * ε m) = 0 := by
  by_cases hee : e = e'
  · subst hee
    have hlm : l ≠ m := fun h => hne (by rw [h])
    calc e * ε l * (e * ε m) = e * e * (ε l * ε m) := by ring
      _ = 0 := by rw [hfo l m hlm, mul_zero]
  · calc e * ε l * (e' * ε m) = (e * e') * (ε l * ε m) := by ring
      _ = 0 := by rw [P.orth e he e' he' hee, zero_mul]

theorem refine_exists {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfi : ∀ l, IsIdempotentElem (ε l)) (hfo : ∀ l m, l ≠ m → ε l * ε m = 0)
    (hfs : ∑ l, ε l = 1) : ∃ Q : PartDiagCut.Part A, P ≤ Q ∧ ∀ g ∈ Q.1, ∃ l, g * ε l = g := by
  classical
  let F : A × Fin n → A := fun x => x.1 * ε x.2
  let T := (P.1 ×ˢ (Finset.univ : Finset (Fin n))).filter (fun x => F x ≠ 0)
  have memT : ∀ x ∈ T, x.1 ∈ P.1 ∧ F x ≠ 0 := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hx.2⟩
  have idF : ∀ x ∈ T, IsIdempotentElem (F x) := fun x hx => (P.idem x.1 (memT x hx).1).1.mul (hfi x.2)
  have oF : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → F x * F y = 0 := fun x hx y hy hxy =>
    orthF P ε hfo (memT x hx).1 (memT y hy).1 (by simpa using hxy)
  have inj : Set.InjOn F T := by
    intro x hx y hy hxy
    by_contra hne
    apply (memT x hx).2
    rw [← (idF x hx).eq]
    nth_rewrite 2 [hxy]
    exact oF x hx y hy hne
  refine ⟨⟨T.image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨idF x hx, (memT x hx).2⟩
  · intro g hg g' hg' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
    exact oF x hx y hy (fun h => hne (by rw [h]))
  · rw [Finset.sum_image inj, Finset.sum_filter_ne_zero, Finset.sum_product]
    simp only [F]
    simp_rw [← Finset.mul_sum, hfs, mul_one]
    exact P.sum_eq
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨x.1, (memT x hx).1, ?_⟩
    show x.1 * ε x.2 * x.1 = x.1 * ε x.2
    rw [mul_right_comm, (P.idem x.1 (memT x hx).1).1.eq]
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨x.2, by show x.1 * ε x.2 * ε x.2 = x.1 * ε x.2; rw [mul_assoc, (hfi x.2).eq]⟩

variable {B : Type} [CommRing B]

theorem natHom (I : Ideal B) {P Q : PartDiagCut.Part (B ⧸ I)} (h : P ≤ Q) :
    (stageMap I h).comp (βP I P) = βP I Q := by
  refine RingHom.ext fun x => funext fun g => ?_
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact IsLocalization.map_eq _ _

theorem isUnit_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (g : Q.1) (x : B) (hx : x ∈ S I g.1) :
    IsUnit (βP I Q x g) := by
  simpa [βP] using IsLocalization.map_units (Localization (S I g.1)) (⟨x, hx⟩ : S I g.1)

theorem mem_of_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I Q)
    (hz : ∀ g : Q.1, ∃ w ∈ I.map (βP I Q), ∃ c : Localization (S I g.1), z g = c * w g) :
    z ∈ I.map (βP I Q) := by
  classical
  rw [← Finset.univ_sum_single z]
  refine Ideal.sum_mem _ fun g _ => ?_
  obtain ⟨w, hw, c, hc⟩ := hz g
  have : (Pi.single g (z g) : PiLocalization₂ I Q) = (Pi.single g c : PiLocalization₂ I Q) * w := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [hc]
    · simp [hg]
  rw [this]; exact Ideal.mul_mem_left _ _ hw

theorem Lift_of : LateralTheory.E.PartCPf.Lift := by
  classical
  intro B _ I P p a₀ n r f hp hfi hfo hfs hy
  obtain ⟨Q, h, hL⟩ := refine_exists P (fun l => Ideal.Quotient.mk I (f l)) hfi hfo hfs
  choose L hLg using fun g : Q.1 => hL g.1 g.2
  refine ⟨Q, h, fun g => stageMap I h (r (L g)) g, ?_, ?_⟩
  · rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
    funext g
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (L g)) (by simp)
  · apply mem_of_comp
    intro g
    have hw : βP I Q (f (L g)) * stageMap I h (a₀ - r (L g)) ∈ I.map (βP I Q) := by
      have := Ideal.mem_map_of_mem (stageMap I h) (hy (L g))
      rw [Ideal.map_map, natHom, map_mul, ← RingHom.comp_apply, natHom] at this
      exact this
    have hmem : f (L g) ∈ S I g.1 := ⟨1, by rw [mul_one, mul_comm]; exact hLg g⟩
    obtain ⟨u, hu⟩ := isUnit_comp I Q g (f (L g)) hmem
    refine ⟨_, hw, -(↑u⁻¹ : Localization (S I g.1)), ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply, map_sub]
    rw [← hu]
    linear_combination (stageMap I h a₀ g - stageMap I h (r (L g)) g) * u.inv_mul

end LateralTheory.E.LiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPfA
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfA

variable (R : Type) [CommRing R]

def hEq (X : Scheme.{0}) : HomotopyEquiv ((chainsN R).obj (sch.obj X))
    ((ChainComplex.single₀ (Shv R)).obj ((free R).obj (yoneda.obj X))) :=
  ((SimplicialObject.Augmented.ExtraDegeneracy.const (yoneda.obj X)).map (free R)).homotopyEquiv

abbrev Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

def isoQ (X : Scheme.{0}) : (Q R).obj ((chains R).obj (sch.obj X)) ≅ (Q R).obj (LateralTheory.E.LocSecPf.pt R X) :=
  ((ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _).symm ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctor (Shv R)).mapIso (HomotopyCategory.isoOfHomotopyEquiv (hEq R X)) ≪≫
  (ComplexShape.embeddingDownNat.extendHomotopyFunctorFactors (Shv R)).app _ ≪≫
  (Q R).mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0 rfl)

def transIso {K K' L : Cx R} (i : (Q R).obj K ≅ (Q R).obj K') (n : ℤ) :
    CohomologyClass K L n ≃+ CohomologyClass K' L n :=
  (CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).trans
    ({ toFun := fun f => i.inv ≫ f, invFun := fun g => i.hom ≫ g,
       left_inv := fun f => by simp, right_inv := fun g => by simp,
       map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _ } : _ ≃+ _) |>.trans
    (CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).symm

theorem locSecA : LateralTheory.E.LocSecPf.LocSecA := fun R _ X F n => ⟨transIso R (isoQ R X) n⟩

end LateralTheory.E.LocSecPfA
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocalIntegralClosureRoots
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.LocalIntegralClosureRoots

theorem root_mem (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (h : GlobalTheory.EtC.AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ x : K, aeval x p = 0 →
      ∃ a : A, algebraMap A K a = x := by
  intro n
  induction n with
  | zero =>
    intro p hn hp x hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
    subst h1
    simp at hx
  | succ n ih =>
    intro p hn hp x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdvd : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hdvd, map_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hqd hq x h1

theorem isIntegrallyClosed_of_aic (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x ⟨p, hp, hx⟩
  exact root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)

theorem LocAIC_of : NormPf.AICPf.LocAIC := by
  intro X _ hcov
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have : Nonempty V := hVne.to_subtype
  have hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hxU, hU, hA⟩ := hcov x
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have := isIntegrallyClosed_of_aic _ hA
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hR : IsIntegrallyClosed Γ(X, V) := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
    have hy : hV.fromSpec y ∈ V := by
      show hV.fromSpec y ∈ (V : Set X)
      rw [← hV.range_fromSpec]; exact ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P := hV.isLocalization_stalk' y hy
    have := hst (hV.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  have hK : IsAlgClosed X.functionField := by
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨U, hxU, hU, hA⟩ := hcov x.1
    have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    exact NormPf.FFPf.algClosed_of_aic _ _ hA
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  intro p hp hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField))
    (by
      rw [degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField),
        degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hd.ne')
  have hint : IsIntegral Γ(X, V) z := ⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩
  have hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0 := hz
  rw [map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]

end LateralTheory.E.LocalIntegralClosureRoots

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NbIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.NbIsoPf

def FlatMonoLim : Prop := ∀ {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (ι : ∀ j, D.obj j ⟶ Y), (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) →
  (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) →
  ∀ {X : Scheme.{0}} (m : X ⟶ Y), Mono m → Flat m → QuasiCompact m → Set.range m = ⋂ j, Set.range (ι j) →
  ∀ c : Cone D, IsLimit c → Nonempty (c.pt ≅ X)

def SysFM : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
        Mono m ∧ Flat m ∧ QuasiCompact m ∧ Set.range m = ⋂ j, Set.range (ι j)

theorem NbIso_of (hS : SysFM) (hL : FlatMonoLim) : LateralTheory.E.SysPf.NbIso := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, m, hm, hf, hq, hr⟩ := hS W w hW y
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, fun c hc => ?_⟩
  exact hL D ι (fun j => ⟨(h1 j).1, (h1 j).2.1⟩) (fun f => (h2 f).1) m hm hf hq hr c hc

end LateralTheory.E.NbIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemSumNoetherian

def NoetherianLocalChartOverlapFiniteComplement : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type) [Field K]
  [Algebra A K] (B C : Subalgebra A K) (t : K), Charts B C t → B.FG → C.FG →
  ∃ N : Submodule A K, N.FG ∧ Subalgebra.toSubmodule (AdjoinInv B t) ≤
    Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N

def LZIdemPow : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f → ∀ k : ℕ,
  ∃ b ∈ B, ∃ c ∈ C, e - b ∈ mS B ∧ c - f ∈ mS C ∧
    b - c ∈ (IsLocalRing.maximalIdeal A ^ k) • Subalgebra.toSubmodule (AdjoinInv B t)

def LZARStep : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (M : Type) [AddCommGroup M]
  [Module A M] (N P : Submodule A M), N.FG →
  ∃ k : ℕ, 1 ≤ k ∧ (IsLocalRing.maximalIdeal A ^ k) • N ⊓ P ≤ IsLocalRing.maximalIdeal A • P

theorem goal_of (h1 : NoetherianLocalChartOverlapFiniteComplement) (h2 : LZIdemPow) (h3 : LZARStep) :
    LateralTheory.E.IdempotentLiftingAlt.LZIdemSumNoeth := by
  intro A _ _ _ K _ _ B C t hc hB hC e f hp
  obtain ⟨N, hN, hD⟩ := h1 A K B C t hc hB hC
  obtain ⟨k, hk, hAR⟩ := h3 A K N (Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C) hN
  obtain ⟨b, hb, c, hcC, heb, hcf, hbc⟩ := h2 A K B C t hc e f hp k
  have hmk : IsLocalRing.maximalIdeal A ^ k ≤ IsLocalRing.maximalIdeal A := Ideal.pow_le_self (by omega)
  have hbc' := Submodule.smul_mono (le_refl (IsLocalRing.maximalIdeal A ^ k)) hD hbc
  rw [Submodule.smul_sup, Submodule.smul_sup] at hbc'
  obtain ⟨x, hx, n, hn, hxn⟩ := Submodule.mem_sup.mp hbc'
  obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hx
  have hβB : β ∈ B := Submodule.smul_le_right hβ
  have hγC : γ ∈ C := Submodule.smul_le_right hγ
  have hnP : n ∈ Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C := by
    refine Submodule.mem_sup.mpr ⟨b - β, B.sub_mem hb hβB, -(c + γ), C.neg_mem (C.add_mem hcC hγC), ?_⟩
    linear_combination -hxn - hβγ
  have hnm := hAR ⟨hn, hnP⟩
  rw [Submodule.smul_sup] at hnm
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hnm
  have hβm : β ∈ mS B := Submodule.smul_mono_left hmk hβ
  have hγm : γ ∈ mS C := Submodule.smul_mono_left hmk hγ
  have hum : u ∈ mS B := hu
  have hvm : v ∈ mS C := hv
  refine Submodule.mem_sup.mpr ⟨(e - b) + β + u, (mS B).add_mem ((mS B).add_mem heb hβm) hum,
    γ + v + (c - f), (mS C).add_mem ((mS C).add_mem hγm hvm) hcf, ?_⟩
  linear_combination hxn + hβγ + huv

end LateralTheory.E.LZIdemSumNoetherian
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartCPfSplit
section
noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPfSplit

theorem split_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) : LateralTheory.E.PartCPf.Split := by
  intro B _ _ I hB P p hm
  have key : ∀ e : P.1, ∃ g : Fin p.natDegree → Localization (S I e.1),
      p.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) = ∏ l, (X - C (g l)) := by
    intro e
    have h0 : (0:B) ∉ S I e.1 := by
      rintro ⟨t, ht⟩
      apply (P.idem e.1 e.2).2
      simpa using ht.symm
    obtain ⟨hdom, haic⟩ := hLoc B (S I e.1) h0 hB
    have hme := hm.map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
    obtain ⟨s, hs⟩ := hMS _ haic _ hme
    have hcard : s.toList.length = p.natDegree := by
      have := congrArg natDegree hs
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hm.natDegree_map] at this
      simp [this]
    refine ⟨fun l => s.toList.get (Fin.cast hcard.symm l), ?_⟩
    rw [hs]
    conv_lhs => rw [← Multiset.coe_toList s]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [← Fintype.prod_equiv (finCongr hcard) (fun i : Fin s.toList.length => X - C (s.toList.get i)) _ (fun _ => rfl)]
    rw [← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp
  choose g hg using key
  refine ⟨p.natDegree, fun l e => g e l, ?_⟩
  refine Polynomial.ext fun k => funext fun e => ?_
  have h2 : (∏ l, (X - C (fun e => g e l))).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e)
      = ∏ l, (X - C (g e l)) := by simp [Polynomial.map_prod]
  have := congrArg (fun q : (Localization (S I e.1))[X] => q.coeff k) ((hg e).trans h2.symm)
  simpa [coeff_map] using this

theorem PartC_of (hLoc : LateralTheory.E.HensCut.LocAIC) (hMS : LateralTheory.E.HensCut.MonicSplits) (hIP : LateralTheory.E.HensCut.IdemPart)
    (hA : LateralTheory.E.PartDiagCut.PartA) (hl : LateralTheory.E.PartCPf.Lift) : LateralTheory.E.PartDiagCut.PartC :=
  LateralTheory.E.PartCPf.PartC_of' (split_of hLoc hMS) hIP hA hl

end LateralTheory.E.PartCPfSplit
end
end

