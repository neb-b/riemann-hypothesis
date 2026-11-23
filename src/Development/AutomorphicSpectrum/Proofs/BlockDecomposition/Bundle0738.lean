module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeOfIsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc.Glue

theorem ideal_eq_of_le_ker_iff {A : Type} [CommRing A] {I J : Ideal A}
    (h : ∀ (R : Type) [CommRing R] (g : A →+* R), I ≤ RingHom.ker g ↔ J ≤ RingHom.ker g) :
    I = J := by
  apply le_antisymm
  · have := (h (A ⧸ J) (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this
  · have := (h (A ⧸ I) (Ideal.Quotient.mk I)).1 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this

theorem eq_zero_of_affine_restrict {T : Scheme.{0}} {V : T.Opens} (s : Γ(T, V))
    (h : ∀ (W : T.Opens) (_ : IsAffineOpen W) (e : W ≤ V),
      (T.presheaf.map (homOfLE e).op).hom s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext T.sheaf V s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  have hz := h W hW hWV
  have h1 := TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hWV) x hxW s
  refine h1.symm.trans ?_
  erw [hz, map_zero, map_zero]

theorem exists_closed_subscheme (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y),
      (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (rep : ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U),
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔
        J ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  choose J hJ using rep
  have hJ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (R : CommRingCat.{0}) (g : Γ(Y, U) ⟶ R),
      P (Spec R) (Spec.map g ≫ hU.fromSpec) ↔ J U hU ≤ RingHom.ker g.hom :=
    fun U hU R g => hJ U hU R g.hom
  let I : Y.IdealSheafData :=
    { ideal := fun U => J U.1 U.2
      map_ideal_basicOpen := by
        intro U f
        refine ideal_eq_of_le_ker_iff fun R _ g => ?_
        rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
        refine (hJ U.1 U.2 R _).symm.trans (Iff.trans ?_ (hJ _ (Y.affineBasicOpen f).2 R g))
        have e := U.2.map_fromSpec (Y.affineBasicOpen f).2 (homOfLE (Y.basicOpen_le f)).op
        rw [← e, ← Category.assoc, ← Spec.map_comp]
        rfl }
  have key : ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ I ≤ t.ker := by
    intro T t
    have hW : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : T.Opens) (hW : IsAffineOpen W)
        (e : W ≤ t ⁻¹ᵁ U), P (Spec Γ(T, W)) (hW.fromSpec ≫ t) ↔
          J U hU ≤ RingHom.ker (t.appLE U W e).hom := by
      intro U hU W hW e
      rw [← hJ' U hU, IsAffineOpen.SpecMap_appLE_fromSpec t hU hW e]
    constructor
    · intro hP
      refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
      change (t.app U.1).hom a = 0
      refine eq_zero_of_affine_restrict _ fun W hWa e => ?_
      exact (hW U.1 U.2 W hWa e).1 (stab _ _ _ _ hP) ha
    · intro hI
      refine loc T t fun x => ?_
      obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := (⊤ : Y.Opens)) (x := t x) trivial
      obtain ⟨W, hWa, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
        (U := t ⁻¹ᵁ U) (x := x) hxU
      have e : W ≤ t ⁻¹ᵁ U := hWU
      have hk : J U hU ≤ RingHom.ker (t.appLE U W e).hom := fun a ha => by
        have h0 : (t.app U).hom a = 0 := t.ideal_ker_le ⟨U, hU⟩ (hI ⟨U, hU⟩ ha)
        change (T.presheaf.map (homOfLE e).op).hom ((t.app U).hom a) = 0
        rw [h0, map_zero]
      have hp := stab _ _ hWa.isoSpec.hom _ ((hW U hU W hWa e).2 hk)
      have e2 : hWa.isoSpec.hom ≫ hWa.fromSpec = W.ι := by
        rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, e2] at hp
      exact ⟨W, hxW, hp⟩
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T t => (key T t).trans ⟨fun h => ?_, ?_⟩⟩
  · exact ⟨IsClosedImmersion.lift I.subschemeι t (by rwa [I.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)

end GlobalTheory.CompanionTheory.TrivLoc.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernIntegralPolynomialGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernTwist

section Multi

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem mInt_update_add_rsmul (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (a : Fin e) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) (t : ℝ) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update Φ a (P + Q.rsmul t)) g =
      mInt A (Function.update Φ a P) g + t * mInt A (Function.update Φ a Q) g := by
  cases e with
  | zero => exact a.elim0
  | succ e =>
    let s : Equiv.Perm (Fin (e + 1)) := Equiv.swap 0 a
    let τ : Fin e → LocPot X := Fin.tail (Φ ∘ s)
    have hτ : ∀ i, IsPotential A (τ i) := fun i => hΦ _
    have key : ∀ T : LocPot X, mInt A (Function.update Φ a T) g = mInt A (Fin.cons T τ) g := by
      intro T
      rw [← mIntSymm A (Function.update Φ a T) s g]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [s]
      · have hne : s i.succ ≠ a := by
          intro h
          have : i.succ = s a := by rw [← h]; simp [s]
          simp [s] at this
        simp [Function.update_of_ne hne, τ, Fin.tail]
    have hc : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A ((Fin.cons T τ : Fin (e + 1) → LocPot X) i) :=
      fun T hT i => Fin.cases hT hτ i
    have hQt := isPotentialRsmul A t Q hQ
    rw [key, key, key, mIntAdd A P (Q.rsmul t) τ hP hQt hτ g (mIntegrableCont A _ (hc P hP) g hg)
      (mIntegrableCont A _ (hc _ hQt) g hg), mIntRsmul A t Q τ hQ hτ g]

theorem exists_poly_mInt (A : FinHolAtlas e X) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q)
    (g : X → ℝ) (hg : Continuous g) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ R : Polynomial ℝ, R.natDegree ≤ S.card ∧
      ∀ t : ℝ, mInt A (fun i => if i ∈ S then P + Q.rsmul t else Φ i) g = R.eval t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ g), by simp, fun t => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hup : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A (Function.update Φ a T i) := by
      intro T hT i
      by_cases e' : i = a
      · subst e'; simpa using hT
      · simpa [Function.update_of_ne e'] using hΦ i
    obtain ⟨R₁, d₁, h₁⟩ := ih _ (hup P hP)
    obtain ⟨R₂, d₂, h₂⟩ := ih _ (hup Q hQ)
    refine ⟨R₁ + Polynomial.X * R₂, ?_, fun t => ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine Polynomial.natDegree_add_le_of_degree_le (d₁.trans (Nat.le_succ _)) ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_X_le (R := ℝ)
      omega
    · set Ψ : Fin e → LocPot X := fun i => if i ∈ S then P + Q.rsmul t else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := by
        intro i
        simp only [hΨ]
        split_ifs
        · exact isPotentialAdd A _ _ hP (isPotentialRsmul A t Q hQ)
        · exact hΦ i
      have e₀ : (fun i => if i ∈ insert a S then P + Q.rsmul t else Φ i) =
          Function.update Ψ a (P + Q.rsmul t) := by
        funext i
        by_cases e' : i = a
        · subst e'; simp
        · simp [Function.update_of_ne e', hΨ, e']
      have e₁ : ∀ T : LocPot X, Function.update Ψ a T =
          fun i => if i ∈ S then P + Q.rsmul t else Function.update Φ a T i := by
        intro T
        funext i
        by_cases e' : i = a
        · subst e'; simp [ha]
        · simp [Function.update_of_ne e', hΨ]
      rw [e₀, mInt_update_add_rsmul A Ψ hΨp a P Q hP hQ t g hg, e₁, e₁, h₁, h₂]
      simp

end Multi

theorem chernInt_twist_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r →
      Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf →
      φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ)
        (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧
          ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y Δ Δ₀ L L₀ r r₀ h h₀ φ φ₀ hφ hφ₀
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  have hP : IsPotential R.finAtlas φ.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ)
  have hQ : IsPotential R.finAtlas φ₀.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ₀)
  obtain ⟨Pol, hdeg, hev⟩ := exists_poly_mInt R.finAtlas φ.locPot φ₀.locPot hP hQ (fun _ => 1) continuous_const
    Finset.univ (fun _ => φ.locPot) (fun _ => hP)
  refine ⟨Pol, by simpa using hdeg, fun m => ?_⟩
  have hpr := h.tens (GlobalTheory.CombChern.presents_zpow h₀ (m : ℤ))
  rw [natCast_zsmul] at hpr
  have hψ : (φ.tens (φ₀.zpow (m : ℤ))).IsCInf := hφ.tens (hφ₀.zpow _)
  refine ⟨_, _, φ.tens (φ₀.zpow (m : ℤ)), hpr, hψ, ?_⟩
  have hT := isPotentialAdd R.finAtlas _ _ hP (isPotentialRsmul R.finAtlas (m : ℝ) _ hQ)
  have hsf : SameForm R.finAtlas (φ.tens (φ₀.zpow (m : ℤ))).locPot (φ.locPot + φ₀.locPot.rsmul (m : ℝ)) := by
    refine Weight.sameForm_of_eq _ hA hT fun x => ?_
    refine ⟨(pick φ.isLB x, fun _ => pick φ₀.isLB x), mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick φ₀.isLB x)⟩,
      fun z => ?_⟩
    have e := φ₀.zpow_φ (m : ℤ) (fun _ => pick φ₀.isLB x) z
    change (φ.φ (pick φ.isLB x) z + (φ₀.zpow (m : ℤ)).φ (fun _ => pick φ₀.isLB x) z) / 2 =
      φ.φ (pick φ.isLB x) z / 2 + (m : ℝ) * (φ₀.φ (pick φ₀.isLB x) z / 2)
    rw [e]
    push_cast
    ring
  rw [((Weight.chernInt_eq_mInt R hψ measurable_const).2
    (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y _ hψ)), SameForm.mInt_eq (fun _ => hsf)]
  simpa using hev (m : ℝ)

end GlobalTheory.CompanionTheory.ChernTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFinite
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FlatFibre

theorem closed_fibre_first_cohomology_finite : FlatBCSt → ∀ (k : Type) [Field k] (A : Over (Sp k)) [IsSeparated A.hom] [QuasiCompact A.hom],
    Module.Finite k (HO1 A.hom) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Sp R ⟶ Sp k)
    (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ (A ⊗ Over.mk t).left),
    IsPullback φ s' (snd A (Over.mk t)).left (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
    Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
      Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ Module.finrank k (HO1 A.hom) := by
  intro hBC k _ A _ _ hfin R _ _ t X' s' φ h
  let u : Sp (IsLocalRing.ResidueField R) ⟶ Sp k :=
    spMap (algebraMap R (IsLocalRing.ResidueField R)) ≫ t
  let σ : k →+* IsLocalRing.ResidueField R := (Spec.preimage u).hom
  have hσ : spMap σ = u := Spec.map_preimage u
  let _ : Algebra k (IsLocalRing.ResidueField R) := σ.toAlgebra
  have hsq : IsPullback (fst A (Over.mk t)).left (snd A (Over.mk t)).left A.hom t := by
    simpa using IsPullback.of_hasPullback A.hom t
  have hp : IsPullback (φ ≫ (fst A (Over.mk t)).left) s' A.hom
      (spMap (algebraMap k (IsLocalRing.ResidueField R))) := by
    have h2 := IsPullback.paste_horiz h hsq
    have h3 : spMap (algebraMap k (IsLocalRing.ResidueField R)) = u := hσ
    rw [h3]
    exact h2
  obtain ⟨e, -⟩ := hBC k (IsLocalRing.ResidueField R) A.left X' A.hom s' _ hp inferInstance inferInstance
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.CompanionTheory.FlatFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeTheoremOfPerfect
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.CubePerf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen GlobalTheory.Biadditive GlobalTheory.CubeNoeth GlobalTheory.CubeModel
attribute [local instance] Over.cartesianMonoidalCategory

section Fibres

variable {X Y T : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem fibTriv_clopen (p : Y ⟶ T)
    (h : ∀ (R : Type) [CommRing R] (j : Spec (CommRingCat.of R) ⟶ T), ∃ (W : Scheme.{0}) (q : W ⟶ Y)
      (f : W ⟶ Spec (CommRingCat.of R)), IsPullback q f p j ∧
      IsClosed {x : PrimeSpectrum R | ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
        (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
        Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π)} ∧
      ∀ (F : Type) [Field F] (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W) (f' : Z ⟶ Spec (CommRingCat.of F)),
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) →
        ∃ r : R, g r ≠ 0 ∧
          Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull (f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι)) :
    fibTriv L φ ε p ⊆ locTriv L φ ε p ∧ IsClosed (fibTriv L φ ε p) := by
  have chart : ∀ t : T, ∃ (R : Type) (_ : CommRing R)
      (j : Spec (CommRingCat.of R) ⟶ T) (_ : IsOpenImmersion j)
      (x : PrimeSpectrum R), j x = t := fun t => by
    obtain ⟨_, ⟨U, hU, rfl⟩, ht, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
    obtain ⟨x, hx⟩ := hU.range_fromSpec.ge ht
    exact ⟨Γ(T, U), inferInstance, hU.fromSpec, hU.isOpenImmersion_fromSpec, x, hx⟩
  constructor
  · intro t ht
    obtain ⟨R, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, -, ho⟩ := h R j
    obtain ⟨F, _, g, Z, π, f', hk, hp, ht⟩ := (mem_fibTriv_iff L φ ε H x).1 ht
    obtain ⟨r, hr, hT⟩ := ho F g Z π f' hp ht
    rw [triv_pull_comp_iff] at hT
    have : IsOpenImmersion q := MorphismProperty.of_isPullback H.flip ‹_›
    refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen r), ⟨x, ?_, rfl⟩, ?_⟩
    · show r ∉ x.asIdeal
      rw [← hk]; exact hr
    · have := hT.comp (IsOpenImmersion.lift ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι ≫ q)
        (p ⁻¹ᵁ (j ''ᵁ (PrimeSpectrum.basicOpen r))).ι (by
          rintro _ ⟨y, rfl⟩
          obtain ⟨x', hx', e⟩ := y.2
          obtain ⟨w, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback H y.1 x' e.symm
          exact ⟨⟨w, (congrArg (· ∈ PrimeSpectrum.basicOpen r) h₂).mpr hx'⟩, h₁⟩))
      exact (congrArg (TrivAt L φ ε) (IsOpenImmersion.lift_fac _ _ _)).mp this
  · refine ⟨isOpen_iff_forall_mem_open.2 fun t ht => ?_⟩
    obtain ⟨R, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, hc, -⟩ := h R j
    refine ⟨j '' _, ?_, j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl, x,
      fun hx => ht ((mem_fibTriv_iff L φ ε H x).2 hx), rfl⟩
    rintro _ ⟨y, hy, rfl⟩ hy'
    exact hy ((mem_fibTriv_iff L φ ε H y).1 hy')

end Fibres

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem triv_of_faces (hP : GlobalTheory.SpreadingModels.PerfAll) (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → ((G3 A).left ⟶ X)) (ε : K → ℤ)
    (face : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → TrivAt M φ ε r)
    (formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (b : Z ⟶ S),
      r ≫ (x3 A 0).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
        ∏ i, k (r ≫ φ i) ^ ε i = 1) :
    Triv (LB.LinComb M φ ε) := by
  have := hA.geomConnected
  have := hA.smooth
  have H := fibTriv_clopen M φ ε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf : ∀ N : LB (B ⊗ B).left, N.IsLB → Nonempty (Perf (B ⊗ B).hom N) := fun N hN' =>
      hP R _ (B ⊗ B).hom sm pr N hN'
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' => CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine face _ 1 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine face _ 0 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M φ ε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M φ ε (x3 A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = S.fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm)⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM φ ε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => formal _ (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

theorem cube (hP : GlobalTheory.SpreadingModels.PerfAll) (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB)
    (T : Over S) (a b c : T ⟶ A) :
    Triv (LB.LinComb L (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]) := by
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ A.left) → U),
        ∏ i, k (r ≫ pts (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, -1, 1, 1, 1, -1] : Fin 8 → ℤ) i = 1 := by
    intro Z r i b h U _ k
    obtain ⟨w, hw, h'⟩ := GlobalTheory.Biadditive.exists_over r i b h
    have := prod_pts (w ≫ x3 A 0) (w ≫ x3 A 1) (w ≫ x3 A 2) (by
      fin_cases i
      exacts [Or.inl h', Or.inr (Or.inl h'), Or.inr (Or.inr h')]) U k
    simp only [← comp_pts, hw] at this
    exact this
  obtain ⟨t, ht⟩ := triv_of_faces hP GlobalTheory.laws_without_cohomology.1 hA hL
    (pts (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, -1, 1, 1, 1, -1]
    (fun r i b h ↦ trivAt_of_formal hL r (formal r i b h)) (fun r b h ↦ formal r 0 b h)
  have c₀ : TrivAt L (pts (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, -1, 1, 1, 1, -1] (lift a (lift b c)).left :=
    ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k ↦ (lift a (lift b c)).left ≫ pts (x3 A 0) (x3 A 1) (x3 A 2) k) = pts a b c := funext fun k ↦ by
    rw [comp_pts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  exact c₀

theorem cubeTheorem_of_perfAll : GlobalTheory.SpreadingModels.PerfAll → GlobalTheory.Published.CubeTheorem := fun hP S A _ hA L hL T a b c =>
  cube hP hA L hL T a b c

end GlobalTheory.CompanionTheory.CubePerf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyRankOverField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField

theorem vb_of_field (hFlat : FlatBCSt) (hLe : PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe) (hGe : H1DimGeAbelianDim) (k : Type) [Field k]
    (A : Over (Sp k)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hsm : SmoothOfRelativeDimension g A.hom) : VB k (HO1 A.hom) g := by
  let K := AlgebraicClosure k
  have hφ := isGrpPullback_pullback A (spMap (algebraMap k K))
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hsm' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap k K))).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hφ.1 hsm
  obtain ⟨hfin, hle⟩ := hLe k A g hab hsm
  obtain ⟨hfin', hle'⟩ := hLe K _ g hab' hsm'
  have hge := hGe K _ g hab' hsm' hfin'
  have := hab.proper
  obtain ⟨e, -⟩ := hFlat k K _ _ A.hom _ _ hφ.1 inferInstance inferInstance
  have hrank : Module.finrank k (HO1 A.hom) = g := by
    have h1 := e.finrank_eq
    rw [Module.finrank_baseChange] at h1
    omega
  refine ⟨hfin, inferInstance, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
  rfl

theorem first_cohomology_rank_over_field : FlatBCSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe → H1DimGeAbelianDim → H1StructureFieldDim := by
  intro hFlat hLe hGe R _ A _ g hab hsm hR
  letI := hR.toField
  exact vb_of_field hFlat hLe hGe R A g hab hsm

end GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField
end
end

