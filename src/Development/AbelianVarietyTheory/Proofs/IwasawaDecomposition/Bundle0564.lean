module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvex

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoisotropicSublatticeOfTorsionCountStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coisotropic_sublattice_of_torsion_count : ∀ (r r₀ : ℕ) (M : Matrix (Fin r) (Fin r) ℤ) (A : Fin r₀ → Fin r → ℤ), M.det ≠ 0 → LinearIndependent ℚ (fun i j => (A i j : ℚ)) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ r ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → (N : ℤ) ∣ (∑ i, a i • A i) ⬝ᵥ M *ᵥ (∑ i, a' i • A i)) → ∀ v : Fin r → ℝ, (∀ i, v ⬝ᵥ (M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (A i j : ℝ)) = 0) → v ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)) := by
  first | exact @GlobalTheory.CoisoCount.coisotropic_of_torsion_count | exact GlobalTheory.CoisoCount.coisotropic_of_torsion_count | (intros; apply GlobalTheory.CoisoCount.coisotropic_of_torsion_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef


open IsLocalRing in
theorem isEtaleCompletion_comp_bij {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : Toroidal.IsEtaleCompletion φ) : Toroidal.IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AtMember


set_option synthInstance.maxHeartbeats 400000 in
theorem conj_gen_mem_frame : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  intro B f T w Z t k
  have hpi : (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG := by
    have h5 : (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = (t.C.herm.levelZeroCompatibility (w.D Z).u₀).piG :=
      congrArg (fun X : Formalism.L2.Herm.ColsHermS (w.D Z) => (X.levelZeroCompatibility (w.D Z).u₀).piG) t.full.2
    exact h5.trans ((t.C.piG (w.D Z).u₀).symm.trans (t.std (w.D Z).u₀).gl.piG)
  show barE (w.D Z) ((Formalism.L2.Herm.toErrXS t.full.1).piG k) ∈
    Ideal.map (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)) ((Fr.at (w.st Z) f).P.pb k).asIdeal
  rw [hpi]
  have hP : (Fr.at (w.st Z) f).P = w.I.C.P := by rw [w.C_eq]; rfl
  rw [hP]
  have hdiv := w.ok.pibar k
  set π : 𝓞 (w.D Z).host.E := w.px.piG k with hπdef
  set b : 𝓞 (w.D Z).host.E := barE (w.D Z) π with hbdef
  have hbc : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) = (w.D Z).host.conj (π : (w.D Z).host.E) := barE_eq_conj _ _
  have hprod : π * b = (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) := by
    apply RingOfIntegers.ext
    show ((π : (w.D Z).host.E) * (b : (w.D Z).host.E)) = algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E)
    rw [map_natCast, hbc]
    exact w.px.piG_norm k
  have hg0 : (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact ((w.D Z).host.g_prime k).ne_zero h'
  have hπ0 : π ≠ 0 := fun h => hg0 (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hg0 (by rw [← hprod, h, mul_zero])
  have hbK : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ∈ (w.D Z).host.K := by
    have hπE : ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ≠ 0 := fun h => hπ0 (RingOfIntegers.ext (h.trans (map_zero (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E)).symm))
    have e : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) =
        ((w.D Z).host.g k : (w.D Z).host.E) / ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) := by
      rw [eq_div_iff hπE, mul_comm, hbc]
      exact w.px.piG_norm k
    rw [e]
    exact div_mem (natCast_mem _ _) (w.px.piG_K k)
  set y : 𝓞 (w.D Z).host.K := toOK b hbK with hydef
  have hy : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y = b := algebraMap_toOK b hbK
  rw [← hy]
  apply Ideal.mem_map_of_mem

  have iI : Algebra.IsIntegral (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hPk : ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)).IsPrime := (w.I.C.P.pb k).isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := @Ideal.exists_ideal_over_prime_of_isIntegral (𝓞 (w.D Z).host.K) _ (𝓞 (w.D Z).host.E) _
    (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)).toAlgebra iI
    ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)) hPk ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) (hx.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  have hgQ : π * b ∈ Q := by
    rw [hprod, ← map_natCast (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)), ← Ideal.mem_comap]
    change _ ∈ Ideal.under (𝓞 (w.D Z).host.K) Q
    rw [hQ]
    exact w.I.C.P.pb_over k
  rcases hQp.mem_or_mem hgQ with hπQ | hbQ
  ·
    have hQ'p : (Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E)).IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E) := by
      rw [Ideal.mem_comap]
      show barE (w.D Z) (barE (w.D Z) π) ∈ Q
      rw [barE_barE]; exact hπQ
    let Q' : HeightOneSpectrum (𝓞 (w.D Z).host.E) :=
      ⟨Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E), hQ'p, fun h => hb0 (by rw [h] at hbQ'; exact (Ideal.mem_bot).1 hbQ')⟩
    have hmem : Q' ∈ (B.primes w.px).vG k := (Formalism.L2.Col.mem_divs hb0 Q').2 hbQ'
    have hd := (hdiv Q').1 hmem
    have hu : y ∈ (HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q').asIdeal := by
      show algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q'.asIdeal
      rw [hy]; exact hbQ'
    have hd' : HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q' = w.I.C.P.pb k := hd
    rw [hd'] at hu
    exact hu
  · rw [← hQ]
    have h' : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q := hy.symm ▸ hbQ
    exact h'

end GlobalTheory.AtMember
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCube

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Transport

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem transport (hG : GlobalFnsSt) (hA' : IsAbelianScheme A') (Φ : A' ⟶ A) [IsMonHom Φ]
    {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (M.pull Φ.left)) (hw : w.IsGen)
    (c : LB.Gen (LB.LinComb M (thφ A (x3 A)) thε)) (c' : LB.Gen (LB.LinComb M' (thφ A' (x3 A')) thε))
    (hc : c.IsGen) (hc' : c'.IsGen)
    (n : ∀ (y : (𝟙_ (Over S)).left) J, Good M y J →
      val c (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1)
    (n' : ∀ (y : (𝟙_ (Over S)).left) J, Good M' y J →
      val c' (lift (1 : 𝟙_ (Over S) ⟶ A') (lift 1 1)).left y J = 1)
    {T : Over S} {z : T.left} {J J'} (hJ : Good M z J) (hJ' : Good M' z J') (x x' y : T ⟶ A') :
    val c (lift (x ≫ Φ) (lift (x' ≫ Φ) (y ≫ Φ))).left z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ Φ.left))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * val c' (lift x (lift x' y)).left z J' := by
  let m3 : G3 A' ⟶ G3 A := lift (x3 A' 0 ≫ Φ) (lift (x3 A' 1 ≫ Φ) (x3 A' 2 ≫ Φ))
  let β : (G3 A' ⟶ A') →* (G3 A' ⟶ A) := MonoidHom.mk' (· ≫ Φ) fun a b => MonObj.mul_comp a b Φ
  have hx : ∀ i, m3 ≫ x3 A i = x3 A' i ≫ Φ := fun i => by fin_cases i <;> simp [m3, x3]
  have comm : ∀ I : thK.{0}, m3.left ≫ thφ A (x3 A) I = thφ A' (x3 A') I ≫ Φ.left := fun I => by
    have e : m3 ≫ psum A (x3 A) I.down = psum A' (x3 A') I.down ≫ Φ :=
      (psum_hom (Geo.Tor.preHom m3) (x3 A) I.down).trans ((congrArg (fun q => psum A q I.down) (funext hx)).trans
        (psum_hom β (x3 A') I.down).symm)
    exact congrArg (fun q => q.left) e
  have q : ∀ {T : Over S} (a b d : T ⟶ A'),
      (lift a (lift b d)).left ≫ m3.left = (lift (a ≫ Φ) (lift (b ≫ Φ) (d ≫ Φ))).left := fun a b d => by
    rw [← Over.comp_left]; congr 1; simp [m3, x3]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hM hM' c' hc'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 A').left) (z : Z) J J', Good M z J → Good M' z J' →
      val t r z J = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z
        (J ((r ≫ thφ A' (x3 A') I) ≫ Φ.left)) (J' (r ≫ thφ A' (x3 A') I)) ^ thε I) * val c' r z J' :=
    fun Z r z J J' hJ hJ' => by
      refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans
        (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
      rw [Category.assoc]
  let e : 𝟙_ (Over S) ⟶ G3 A' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA' _) (surj_comp (surj_snd hG hA' _) (hG _ _ hA').2)
  have he : e.left ≫ (snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hM (φ := fun I => m3.left ≫ thφ A (x3 A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (comm I).symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hc m3.left) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over S)).left ⟶ A'.left => exists_chart hM' (χ y)
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A') 1 1 (fun q => gw w q y (I (q ≫ Φ.left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (n' y I' hI'))).symm
      rw [val_pull hI, q, MonObj.one_comp, n y I hI]
      simp) _ (lift x (lift x' y)).left z J hJ
  rw [val_pull hJ, q] at key
  exact key.trans (hv' _ _ z J J' hJ hJ')

end Transport

section Chart

variable {X Y : Scheme.{0}} {L : LB X}

theorem good_sq {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) y (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => by simpa using hJ ψ

theorem adj_sq (hL : L.IsLB) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (χ : Y ⟶ X) :
    adj (fun _ : Fin 1 => 𝟙 X) (fun _ => (2 : ℤ)) y (fun q _ => J q) J χ = 1 := by
  have m := hJ.mem (fun _ : Fin 1 => 𝟙 X) χ
  simp only [Category.comp_id] at m
  unfold adj
  simp only [Category.comp_id]
  exact trF_self hL _ _ χ y m

end Chart

section Square

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem sq_formEq : FormEq (Sum.elim (thφ G (x3 G)) (thφ G (x3 G))) (Sum.elim thε thε)
    (flatφ (fun _ : Fin 1 => 𝟙 G.left) (thφ G (x3 G))) (flatε (fun _ : Fin 1 => (2 : ℤ)) thε) := fun U _ h => by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
  rw [zpow_mul, zpow_two]

theorem exists_sqCube {L : RigLB G} (c : CubicalStr G L) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (thφ G (x3 G)) thε),
      u.IsGen ∧ (∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val u (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2) ∧
      ∀ (y : (𝟙_ (Over S)).left) JP, Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        val u (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y JP = 1 := by
  obtain ⟨s, hs, hv⟩ := exists_gen L.isLB sq_formEq (LB.mulGen L.L (thφ G (x3 G)) thε (thφ G (x3 G)) thε c.t c.t)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ c.isGen c.isGen)
  have F : ∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val (nest L.L _ _ _ _ s) (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2 := fun y J hJ JP hJP a b d => by
    rw [val_nest hs _ hJP hJ, hv _ _ y J hJ]
    exact congrArg _ ((val_mul hJ _ _ _).trans (sq _).symm)
  refine ⟨nest L.L _ _ _ _ s, nest_isGen hs, F, fun y JP hJP => ?_⟩
  choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ G.left => exists_chart L.isLB (χ y)
  change ((𝟙_ (Over S)).left ⟶ G.left) → Fin 1 → L.L.ι at JP
  set_option backward.isDefEq.respectTransparency false in
  have hcub : cubV c y J (1 : 𝟙_ (Over S) ⟶ G) 1 1 = 1 :=
    by
      have h := val_corr hJ (c.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [val_one, val_pull hJ _ _ _, ← Over.comp_left] at h
      convert h using 1 <;> simp [cubV, faceMap, x2, pzero, Hom.one_def]
  rw [F y J hJ JP hJP]
  rw [prod_cub, hcub]
  simp

end Square

end GlobalTheory.SqCube

theorem GlobalTheory.cube_sq_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  intro R _ _ _ _ D D' Φ w hw hΦ T z J J' hJ hJ' Ω hΩ a b c
  subst hΩ
  obtain ⟨u, hu, hvu, nu⟩ := GlobalTheory.SqCube.exists_sqCube D.toPre.cub
  obtain ⟨u', hu', hvu', nu'⟩ := GlobalTheory.SqCube.exists_sqCube D'.toPre.cub
  have key := GlobalTheory.SqCube.transport GlobalTheory.globalFns_holds D'.toPre.P.isAb Φ.hom
    (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (DVR.linComb_isLB _ D'.toPre.P.isLB _ _) w hw u u' hu hu' nu nu'
    (GlobalTheory.SqCube.good_sq hJ) (GlobalTheory.SqCube.good_sq hJ') a b c
  rw [hvu z J hJ _ (GlobalTheory.SqCube.good_sq hJ), hvu' z J' hJ' _ (GlobalTheory.SqCube.good_sq hJ')] at key
  simp only [GlobalTheory.SqCube.adj_sq D.toPre.P.isLB hJ, GlobalTheory.SqCube.adj_sq D'.toPre.P.isLB hJ', one_zpow,
    Finset.prod_const_one, _root_.one_mul] at key
  refine key.trans ?_
  rw [prod_cub a b c (fun q => gw w q z (fun _ => J (q ≫ Φ.hom.left)) (fun _ => J' q))]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC


set_option maxHeartbeats 4000000 in
theorem lift_lattice_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix h1 h2 h3 h4 h5 h6 h7) (StepW.of_all fun K B' f' T' w' _ _ hQ => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  obtain ⟨e, C, hC, hθ⟩ := hQ B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  have hstar : ∀ x, φ (star x) = star (φ x) := fun x => (w'.st Z').toD7.what₂.embLL.injective (by
    rw [hφ, (w.st Z).toD7.starLL_cx, (w'.st Z').toD7.starLL_cx, hφ])
  obtain ⟨N, hN, hTl, hF⟩ := _root_.GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt φ hstar e _ _ _ _ _ _ 1 C (hL.ok.ok2.lifts j _) hC
  refine ⟨N, hN, hTl, fun x => ?_⟩
  refine HEq.trans (heq_of_eq (tC_cpt (z'.R.toCx3 z'.F) z'.F.cr false j' _ _)) (HEq.trans ?_ (heq_of_eq (tC_cpt (z.R.toCx3 z.F) z.F.cr false j _ x)).symm)
  have e1 : z'.F.cr.toL (z'.R.toCx3 z'.F).zs false j' _ (Matrix.mulVec N fun k => φ (x k)) =
      GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C (z.F.cr.toL (z.R.toCx3 z.F).zs false j _ x) := hF x
  exact HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) e1)) (hθ _)

end GlobalTheory.Mem.R3.LiftLatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

theorem zeroPt_sc {S : Type} [CommRing S] (c : S) : GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc c = GlobalTheory.PowLie.zeroPt S := by
  ext1
  simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  simp [epsScaleR]

theorem isTangent_prod {S : Type} [CommRing S] {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {n : ℕ}
    (v : Fin n → (epsR S ⟶ G')) (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) :
    IsTangent (∏ k, GlobalTheory.PowLie.sc (c k) ≫ v k) := by
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G') (GlobalTheory.PowLie.zeroPt S)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ
  refine (e.trans ?_)
  refine (Finset.prod_eq_one fun k _ => ?_).trans rfl
  change GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, zeroPt_sc, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  intro S _ X x G G' _ _ _ φ h n v hv V hA hV b hb
  set w₀ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc (b k) ≫ v k with hw₀
  set w₁ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc ((0 : Fin n → S) k) ≫ v k with hw₁
  have c₀ : IsLieComb b v w₀ := (GlobalTheory.PowLie.isLieComb_iff_prod b v w₀).2 rfl
  have c₁ : IsLieComb 0 v w₁ := (GlobalTheory.PowLie.isLieComb_iff_prod 0 v w₁).2 rfl
  have t₀ : IsTangent w₀ := isTangent_prod v hv.1 b
  have t₁ : IsTangent w₁ := isTangent_prod v hv.1 0
  have l₀ := tan_le h w₀ t₀ V hV
  have l₁ := tan_le h w₁ t₁ V hV
  have fst_eq : ∀ (w : epsR S ⟶ G'), IsTangent w → ∀ f : Γ(G.left, V),
      (valR (w.left ≫ φ) V f).fst = valR ((η[G']).left ≫ φ) V f := by
    intro w hw f
    have e1 := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom S S S).toRingHom (w.left ≫ φ) V (tan_le h w hw V hV) f
    have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (η[G']).left ≫ φ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ) hw
    rw [e2] at e1
    rw [e1]
    rfl
  have e : w₀.left ≫ φ = w₁.left ≫ φ := by
    refine GlobalTheory.HolHom.point_ext hA l₀ l₁ fun f => ?_
    refine TrivSqZeroExt.ext ((fst_eq w₀ t₀ f).trans (fst_eq w₁ t₁ f).symm) ?_
    rw [comb_snd h v hv.1 b w₀ c₀ V hV f, comb_snd h v hv.1 0 w₁ c₁ V hV f, hb f]
    simp
  have hw : w₀ = w₁ := ReciprocityTheory.ChartRestriction.G.Chart.inj_over h e
  exact (hv.2 w₀ t₀).unique c₀ (hw ▸ c₁)

end GlobalTheory.ArcLieCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)), IsOpen B → Convex ℝ B → (∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) → ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | exact GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global <;> assumption)
end

