module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariant
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.LeviConstTerm

theorem setIntegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃ₜ+ G) (hT : ∀ x ∈ Γ, T x ∈ Γ)
    (hT' : ∀ x ∈ Γ, T.symm x ∈ Γ) (h : G → ℂ) (hinv : ∀ (γ : Γ) (x : G), h (γ +ᵥ x) = h x) :
    ∫ x in 𝓕, h (T x) ∂μ = ∫ x in 𝓕, h x ∂μ := by
  have key : ∀ U : G ≃ₜ+ G, (∀ x ∈ Γ, U x ∈ Γ) → (∀ x ∈ Γ, U.symm x ∈ Γ) →
      MeasurePreserving U μ μ ∧ IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
    intro U hU hU'
    have hmeas : Measurable U := U.continuous.measurable
    haveI : (μ.map U).IsAddHaarMeasure := U.isAddHaarMeasure_map μ
    have hc := Measure.isAddLeftInvariant_eq_smul (μ.map U) μ
    have hq : Measure.QuasiMeasurePreserving U μ μ := ⟨hmeas.aemeasurable, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
    have hS : IsAddFundamentalDomain Γ (U ⁻¹' 𝓕) μ := by
      refine h𝓕.preimage_of_equiv (e := fun γ : Γ => (⟨U.symm γ, hU' _ γ.2⟩ : Γ)) hq ?_ ?_
      · refine ⟨fun x y hxy => Subtype.ext (U.symm.injective (congrArg Subtype.val hxy)), fun y => ⟨⟨U y, hU _ y.2⟩, ?_⟩⟩
        exact Subtype.ext (U.symm_apply_apply _)
      · intro γ x
        change U (U.symm γ + x) = (γ : G) + U x
        rw [map_add (f := _), U.apply_symm_apply]
    refine ⟨⟨hmeas, ?_⟩, hS⟩
    have h2 : μ (U ⁻¹' 𝓕) = 1 := (hS.measure_eq h𝓕).trans h1
    have h3 : μ.map U 𝓕 = 1 := by
      rw [Measure.map_apply₀ hmeas.aemeasurable (h𝓕.nullMeasurableSet.mono_ac hq.2), h2]
    rw [hc, Measure.smul_apply, h1] at h3
    have h4 : (μ.map U).addHaarScalarFactor μ = 1 := by
      simpa [ENNReal.smul_def] using h3
    rw [hc, h4, one_smul]
  have hmp := (key T hT hT').1
  have hS := (key T.symm hT' hT).2
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hpre : T ⁻¹' (T.symm ⁻¹' 𝓕) = 𝓕 := by ext x; simp
  calc ∫ x in 𝓕, h (T x) ∂μ = ∫ x in T ⁻¹' (T.symm ⁻¹' 𝓕), h (T x) ∂μ := by rw [hpre]
    _ = ∫ x in T.symm ⁻¹' 𝓕, h x ∂μ := hmp.setIntegral_preimage_emb hemb h _
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

variable {R : Type} [CommRing R] {a r : ℕ}

def IsBlockSL2Embedding (r : ℕ) (m : Matrix (Fin a) (Fin a) R) : Prop :=
  ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m i j = 0

def conjN (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (m * nilM x * n) p.1.1 p.1.2

theorem nilM_conjN {m n : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n) (x : BlockIx a r → R) :
    nilM (conjN m n x) = m * nilM x * n := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simp only [nilM, Matrix.of_apply, dif_pos h]; rfl
  · rw [nilM, Matrix.of_apply, dite_eq_right h, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rcases hn k j with h1 | h1
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro l _
      rcases hm i l with h2 | h2
      · rw [nilM, Matrix.of_apply, dite_eq_right (fun h' => h (by omega)), mul_zero]
      · rw [h2, zero_mul]
    · rw [h1, mul_zero]

theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem conjN_add (m n : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    conjN m n (x + y) = conjN m n x + conjN m n y := by
  funext p
  simp only [conjN, nilM_add, mul_add, add_mul, Matrix.add_apply, Pi.add_apply]

theorem conjN_conjN {m n m' n' : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) (hn : IsBlockSL2Embedding r n)
    (h1 : m' * m = 1) (h2 : n * n' = 1) (x : BlockIx a r → R) : conjN m' n' (conjN m n x) = x := by
  funext p
  have : m' * (m * nilM x * n) * n' = nilM x := by
    rw [show m' * (m * nilM x * n) * n' = (m' * m) * nilM x * (n * n') by simp only [mul_assoc], h1, h2, one_mul,
      mul_one]
  rw [conjN, nilM_conjN hm hn, this, nilM, Matrix.of_apply, dif_pos p.2]

theorem continuous_conjN [TopologicalSpace R] [IsTopologicalRing R] (m n : Matrix (Fin a) (Fin a) R) :
    Continuous (conjN (r := r) m n) := by
  have h : Continuous (nilM : (BlockIx a r → R) → Matrix (Fin a) (Fin a) R) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine continuous_pi fun p => ?_
  exact ((continuous_const.matrix_mul h).matrix_mul continuous_const).matrix_elem _ _

theorem conjN_map {S : Type} [CommRing S] (φ : R →+* S) (m n : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    conjN (m.map φ) (n.map φ) (fun p => φ (x p)) = fun p => φ (conjN m n x p) := by
  have : nilM (fun p => φ (x p)) = (nilM x).map φ := by
    ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp
  funext p
  rw [conjN, conjN, this, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

theorem IsBlockSL2Embedding.map {S : Type} [CommRing S] (φ : R →+* S) {m : Matrix (Fin a) (Fin a) R} (hm : IsBlockSL2Embedding r m) :
    IsBlockSL2Embedding r (m.map φ) := fun i j => (hm i j).imp id fun h => by rw [Matrix.map_apply, h, map_zero]

theorem unip_mul (m : GL (Fin a) R) (hm : IsBlockSL2Embedding r m.val) (hm' : IsBlockSL2Embedding r m⁻¹.val) (x : BlockIx a r → R) :
    unip x * m = m * unip (conjN m⁻¹.val m.val x) := by
  apply Units.ext
  change (1 + nilM x) * m.val = m.val * (1 + nilM (conjN m⁻¹.val m.val x))
  rw [nilM_conjN hm' hm, mul_add, add_mul, one_mul, mul_one, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

theorem constTerm_levi_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (γ : GL (Fin r) E × GL (Fin (a - r)) E) (g : GA E a), ∫ x in 𝓕, f (unip x * (ratGL E a (GlobalTheory.LeviGA.blkGL hr γ) * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 f hf γ g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  obtain ⟨m, hm⟩ : ∃ m, m = GlobalTheory.LeviGA.blkGL hr γ := ⟨_, rfl⟩
  have hb : IsBlockSL2Embedding r m.val := hm ▸ GlobalTheory.LeviGA.blkGL_block hr γ
  have hb' : IsBlockSL2Embedding r m⁻¹.val := by
    rw [hm, ← map_inv]; exact GlobalTheory.LeviGA.blkGL_block hr γ⁻¹
  rw [← hm]
  have e1 : (ratGL E a m).val = m.val.map (algebraMap E (Ad E)) := rfl
  have e2 : (ratGL E a m)⁻¹.val = m⁻¹.val.map (algebraMap E (Ad E)) := rfl
  have hB : IsBlockSL2Embedding r (ratGL E a m).val := e1 ▸ hb.map _
  have hB' : IsBlockSL2Embedding r (ratGL E a m)⁻¹.val := e2 ▸ hb'.map _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := conjN (ratGL E a m)⁻¹.val (ratGL E a m).val
      invFun := conjN (ratGL E a m).val (ratGL E a m)⁻¹.val
      left_inv := conjN_conjN hB' hB (Units.mul_inv _) (Units.mul_inv _)
      right_inv := conjN_conjN hB hB' (Units.inv_mul _) (Units.inv_mul _)
      map_add' := conjN_add _ _
      continuous_toFun := continuous_conjN _ _
      continuous_invFun := continuous_conjN _ _ }
  have hL : ∀ x, f (unip x * (ratGL E a m * g)) = h (T x) := fun x => by
    rw [← mul_assoc, unip_mul _ hB hB', mul_assoc, hf]; rfl
  simp_rw [hL]
  refine setIntegral_comp_aut (ratN E a r) μ 𝓕 h𝓕 h1 T ?_ ?_ h hinv
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m⁻¹.val m.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩
  · rintro _ ⟨e, rfl⟩
    exact ⟨conjN m.val m⁻¹.val e, (conjN_map (algebraMap E (Ad E)) _ _ e).symm⟩

end GlobalTheory.LeviConstTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfAlternatingSumScaledUnipFD
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

theorem norm_le_of_altSum_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ hinv hcusp hφ M hM x m B hB
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  set H : (BlockIx a r → Ad E) → ℂ := fun s => φ (unip s * x) with hH
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous H := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  have hper : ∀ ξ ∈ ratN E a r, ∀ s, H (ξ + s) = H s := by
    rintro _ ⟨e, rfl⟩ s
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + s) * x) = φ (unip s * x)
    rw [unip_add, unip_algebraMap, mul_assoc, hinv]
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) D ν :=
    fun t => ((hcont.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in D, H y ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hB' : ∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ D) →
      ‖GroundTheory.Automorphic.altSum m H y 0‖ ≤ B := by
    intro y hy
    rw [GroundTheory.Automorphic.altSum_eq_sum]
    simpa [H, zero_add, zsmul_eq_mul] using hB y hy
  have h0 := GroundTheory.Automorphic.norm_le_of_forall_altSum_le hD hD1 m H hper hint hmean B hB'
  have hu0 : (unip (0 : BlockIx a r → Ad E) : GA E a) = 1 := by
    have h := unip_add (0 : BlockIx a r → Ad E) 0
    rw [add_zero] at h
    simpa using h
  have hH0 : H 0 = φ x := by simp only [H, hu0, one_mul]
  rwa [hH0] at h0

end GlobalTheory.CuspTail
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOnEqZeroOfEqOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

open TopForm

namespace TopForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {U : Y.Opens}

theorem dOn_eq_zero_of_eq_one (f : Fin D → Γ(Y, U)) (b : Fin D) (hb : f b = 1) : dOn p f = 0 := by
  rw [dOn, dForm_eq]
  refine AlternatingMap.map_coord_zero _ b ?_
  let := (algX p U).toAlgebra
  rw [hb]
  exact (KaehlerDifferential.D k Γ(Y, U)).map_one_eq_zero

theorem jacOn_of_eq_one (f : Fin (D + 1) → Γ(Y, U)) (i : Fin (D + 1)) (hi : f i = 1) :
    jacOn p f = (-1 : Γ(Y, U)) ^ (i : ℕ) • dOn p fun b => f (i.succAbove b) := by
  rw [jacOn_eq, Finset.sum_eq_single i, hi, mul_one]
  · intro a _ ha
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm ha)
    rw [dOn_eq_zero_of_eq_one _ b (by rw [hb, hi]), smul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem isUnit_of_affine {f : Γ(Y, U)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ U, IsUnit (resG Y hW f)) : IsUnit f := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  have := (h W hW hWU).map (Y.presheaf.germ W x hxW).hom
  rwa [show (Y.presheaf.germ W x hxW).hom (resG Y hWU f) = (Y.presheaf.germ U x hx).hom f from
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW f] at this

theorem isFreeGen_dForm_X (k : Type) [CommRing k] (D : ℕ) : IsFreeGen (MvPolynomial (Fin D) k)
    (dForm (algebraMap k (MvPolynomial (Fin D) k)) (X : Fin D → _)) := by
  have key (inst : Algebra k (MvPolynomial (Fin D) k))
      (e : inst = AddMonoidAlgebra.algebra) :
      IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D X) := by
    subst e
    have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
    rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
  exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)

end TopForm

namespace ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

theorem isFrame_dOn_ratio (i : Fin (N + 1)) :
    IsFrame (dOn (PSpace.str R N) fun b : Fin N => ratio R N i (i.succAbove b)) := by
  refine ⟨isAffineOpen_chart R N i, ?_⟩
  let e : MvPolynomial (Fin N) R ≃ₐ[R] Γ(PSpace R N, chart R N i) :=
    (renameEquiv R (finSuccAboveEquiv i)).trans (chartAlgEquiv R N i)
  have he : (e : MvPolynomial (Fin N) R →+* _).comp (algebraMap R _) =
      algX (PSpace.str R N) (chart R N i) := RingHom.ext fun r => e.commutes r
  have := (isFreeGen_dForm_X R N).formMap (RingHom.Etale.of_bijective e.bijective) he
  rw [formMap_dForm] at this
  convert this using 3 with b
  exact ((congrArg (chartAlgEquiv R N i) (rename_X _ b)).trans
    (chartAlgEquiv_X R N i (finSuccAboveEquiv i b))).symm

theorem isUnit_jacSec_coord [SmoothOfRelativeDimension N (PSpace.str R N)]
    (K : CanonLB (PSpace.str R N) N) (c : (K.adj (O1 R N) (N + 1)).ι) :
    IsUnit ((K.jacSec (coord R N)).f c) := by
  refine isUnit_of_affine fun W hW h => ?_
  have l := h.trans (K.adj_U_le _ c)
  have h₂ : W ≤ chart R N (c.2 PUnit.unit) := l.trans inf_le_right
  rw [K.resG_jacSec_f _ c h (l.trans inf_le_left) h₂]
  change IsUnit (K.coeff _ _ (jacOn _ (ratioOn W (c.2 PUnit.unit) h₂)))
  rw [jacOn_of_eq_one _ (c.2 PUnit.unit) (ratioOn_self (hi := h₂)), map_smul, smul_eq_mul]
  refine (isUnit_one.neg.pow _).mul ((K.isUnit_jacobian_iff _ hW _ _).2 ?_)
  have := (isFrame_dOn_ratio R N (c.2 PUnit.unit)).res hW h₂
  rw [resForm_dOn] at this
  exact this

end ProjSpace

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValInj

theorem eq_zero_of_val_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  intro A _ g L u hA U b hb
  haveI : Smooth A.hom := hA.smooth
  haveI : IsReduced A.left := isReduced_of_smooth A.hom
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  have hzx : (u.ex z).left = x := by rw [hz]; rfl
  have h1 : val u.ex U b z = 0 := hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)
  rw [show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx] at h1
  rw [h1]
  unfold valAt' valAt
  split_ifs <;> simp

end GlobalTheory.ValInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersion
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenRestrictPol

theorem exists_restrict_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S),
    IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left),
    IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
    Out.RelAmple A' (L.pull φ) := by
  intro S A _ _ L hA hL hr hamp V j _
  have hpb := isGrpPullback_pullback A j
  have := hA.proper
  exact ⟨(Over.pullback j).obj A, inferInstance, GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb,
    pullback.fst A.hom j, hpb, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb, pull_isLB hL _,
    GlobalTheory.PolBaseChange.rigidified_pull hpb hr, GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp hpb.1⟩

end GlobalTheory.OpenRestrictPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
end
end

