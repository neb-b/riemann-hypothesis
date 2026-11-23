module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dB_sigmaB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) =
      ((levSys h).L m).σB g ((levSys h).dB m b) := by
  intro m g b
  change Bk l (m + 1 + 1) at b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  show dk l (m + 1) (gB h (m + 1 + 1) g (Ideal.Quotient.mk _ x)) =
    gB h (m + 1) g (dk l (m + 1) (Ideal.Quotient.mk _ x))
  simp only [gB, dk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

end GlobalTheory.CompanionTheory.LatLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphism
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

section Gen
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

theorem map_isDPMorphism (g : B →+* B') (h : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M)
    (hg : g (f ξ) = f' ξ')
    (hc : DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (hc' : DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g h) := by
  have hIB : ∀ x ∈ Lat.IB f ξ, g x ∈ Lat.IB f' ξ' := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]
    exact hIB _ ha
  · intro n a ha
    have ha' : Lat.ι f ξ l M a ∈ Lat.IB f ξ := ha
    have hb : Lat.map f ξ f' ξ' l M g h a ∈ Lat.I f' ξ' l M := by
      show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
      rw [Lat.ι_map]
      exact hIB _ ha'
    apply Lat.ι_injective f' ξ' l M
    rw [Lat.ι_γ _ _ _ _ _ hb, Lat.ι_map, Lat.ι_map, Lat.ι_γ _ _ _ _ _ ha, DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ ha',
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ (hIB _ ha'), map_rat_smul, map_pow]

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem dk_fk (k : ℕ) (w : Ainf l) : dk l k (fk l (k + 1) w) = fk l k w := by
  rfl

theorem levSys_ddp {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (m : ℕ) :
    IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  exact map_isDPMorphism (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1))
    (fun x hx => h.dIn (m + 1) x hx) (dk_fk (m + 1) (xi0 l)) (h.hc (m + 2)) (h.hc (m + 1))

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem toB_on_K : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  intro l _ K M h k a y hy
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) := fun x y h =>
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h
  have key : pInv l y = kP l K a := by
    apply hinj
    have h1 : algebraMap (BdRp l) (BdR l) (pInv l y) = y.1 := by
      have := (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply y
      exact congrArg Subtype.val this
    rw [h1]
    exact hy
  show pk l k (pInv l y) = pk l k (kP l K a)
  rw [key]

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvd
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_toB_ker {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  have ht : (per l K).tB = algebraMap (BdRp l) (BdR l) (tBdR l) := by
    change DeRhamPotentiallySemistable.DRPst.iC l (tA l) = _
    change algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
    rw [show ACris.iota ℂ_[l] l (tA l) = tBdR l from ACris.iota_periodT (untilt_epsilon (p := l))]
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  have hp : ∀ x : ↥(algebraMap (BdRp l) (BdR l)).range, algebraMap (BdRp l) (BdR l) (pInv l x) = x := by
    intro x
    obtain ⟨z, hz⟩ := x.2
    have : pInv l x = z := by
      apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_eq.2
      exact Subtype.ext hz.symm
    rw [this, hz]
  intro x
  change pk l k (pInv l x) = 0 ↔ _
  rw [pk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨algebraMap (BdRp l) (BdR l) z, z, rfl⟩, ?_⟩
    have := hp x
    rw [← hz, map_mul, map_pow, mul_comm] at this
    rw [ht]
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, hinj ?_⟩
    rw [map_mul, map_pow, mul_comm, hp x, hz]
    rw [ht] at hy
    exact hy.symm

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem pInv_algebraMap (l : ℕ) [Fact l.Prime] (b : BdRp l) (hb : algebraMap (BdRp l) (BdR l) b ∈ (algebraMap (BdRp l) (BdR l)).range) :
    pInv l ⟨algebraMap (BdRp l) (BdR l) b, hb⟩ = b := by
  have : (⟨algebraMap (BdRp l) (BdR l) b, hb⟩ : ↥(algebraMap (BdRp l) (BdR l)).range) = (algebraMap (BdRp l) (BdR l)).rangeRestrict b := rfl
  rw [this]
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply b

theorem sigmaB_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y →
      (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  rintro g ⟨_, b, rfl⟩ ⟨y, hy⟩ hxy
  have hy' : y = algebraMap (BdRp l) (BdR l) (gP l g b) := by
    refine (Eq.trans hxy.symm ?_)
    exact galBdRField_algebraMap (toBot g.1) b
  subst hy'
  show gB h k g (pk l k (pInv l ⟨_, _⟩)) = pk l k (pInv l ⟨_, _⟩)
  rw [pInv_algebraMap, pInv_algebraMap]
  rfl

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevels

theorem pInv_surjective (l : ℕ) [Fact l.Prime] : Function.Surjective (pInv l) := by
  intro x
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩
  unfold pInv
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x

theorem toB_surjective {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : Function.Surjective (lev h k).toB := by
  have h1 : Function.Surjective ((pk l k).comp (pInv l)) := by
    rw [RingHom.coe_comp]
    exact (Ideal.Quotient.mk_surjective).comp (pInv_surjective l)
  exact h1

end GlobalTheory.CompanionTheory.LatLevels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompat
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC.Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem ι_lam_ainf (h : LevHyp l K M) (k : ℕ) (w : Ainf l) :
    (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) = fk l k w := by
  show pk l k (ACris.iota ℂ_[l] l (algebraMap (Ainf l) (Acris l) w)) = _
  rw [ACris.iota_algebraMap]
  rfl

theorem pk_mem_of_theta (k : ℕ) {d : BdRp l} (hd : IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l d = 0) :
    pk l k d ∈ IB (fk l k) (xi0 l) := by
  have h1 : d ∈ RingHom.ker (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l) := hd
  rw [IsPerfectoidField.ker_thetaBDeRhamPlusField, ker_thetaBDeRhamPlus ker_theta0,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem xi_and_sub_mem_I (h : LevHyp l K M) (k : ℕ) :
    (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧
      ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
        algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  refine ⟨?_, fun a w hw => ?_⟩
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    rw [ι_lam_ainf]
    exact Ideal.mem_span_singleton_self _
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    have e : (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = pk l k (kP l K (a : K)) := rfl
    have e2 : (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := ι_lam_ainf h k w
    have e3 : (lev h k).ι (algebraMap (OK l K) (lev h k).A a -
        (lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (kP l K (a : K) - wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := by
      rw [map_sub, e, e2, map_sub]
    rw [e3]
    apply pk_mem_of_theta
    rw [map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, sub_eq_zero]
    have := thetaAlgHom_algClToBdR l (K.val (a : K))
    rw [thetaAlgHom_apply] at this
    refine this.trans ?_
    show _ = ((theta0 l w : OC l) : ℂ_[l])
    rw [hw]
    rfl

end GlobalTheory.CompanionTheory.LatC.Red
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensity
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdLat

theorem fibre_masses_standard_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  intro F E _ _ _ _ _ σ hCM J hJ d b v lam hlam m hm
  classical
  have hloc : IsLocR (Fv F v) := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, htr, -, hBorW, -, hgr⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hLc, hLo, -, hL1⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 2 v
  obtain ⟨hSh, -, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  haveI : BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := hBorW 1 2
  haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
  have hLm : MeasurableSet (latV (M := 2) (n := 1) b v) := hLo.measurableSet
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin 2 → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := 2) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, -⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hCM 2 J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m (hW 1 2) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hunit : ∀ z ∈ ({0}ᶜ : Set (Fv F v)),
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact FibreRatio.isUnit_tmul (Fv F v) hz
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal) {0}ᶜ := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  refine ⟨hcont, ?_⟩
  have hfin : ∀ S, m S (latV b v) < ⊤ := fun S => by
    haveI := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hCM 2 J hJ (Fv F v) hloc 1 _ _ m (hW 1 2) (hH 1) hm S).1
    exact hLc.measure_lt_top
  obtain ⟨n1, n2⟩ := _root_.GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hCM 2 J hJ (by norm_num) v (coordW (Fv F v) b lam 1 2) lam (hW 1 2) hlam.1
  have n1' : lam ({0}ᶜ : Set (Fv F v))ᶜ = 0 := by
    refine measure_mono_null (fun c hc => ?_) n1
    have : c = 0 := by simpa using hc
    simp [this]
  have hres : lam.restrict ({0}ᶜ : Set (Fv F v)) = lam :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact n1')
  have hcq : Continuous fun X : Fin 1 → Fin 2 → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 2 J).matrix_elem 0 0))
  have hVm : MeasurableSet ({0}ᶜ : Set (Fv F v)) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} :=
    (FibreRatio.continuous_qS (Fv F v) htr).measurable hVm
  have hmass := FibreRatio.mass_eq_lintegral (Fv F v) hCM hJ hm hLm (V := {0}ᶜ) (by simp) (hcq.measurable hVm) hP
  have hconull : coordW (Fv F v) b lam 1 2 {X : Fin 1 → Fin 2 → Fv F v ⊗[F] E | algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ ({0}ᶜ : Set (Fv F v))}ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) n2
    have h0 : algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) = 0 := by simpa using hX
    intro hu
    exact hu.ne_zero h0
  rw [measure_inter_conull hconull, hL1 lam hlam, ← hSm lam hlam.1] at hmass
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  rw [hEmb.restrict_map, hEmb.lintegral_map] at hmass
  have hpre : hermScal (Fv F v) σ ⁻¹' {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} = {0}ᶜ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, FibreRatio.qS_hermScal (Fv F v) hCM s]
  rw [hpre, hres] at hmass
  have hae : AEMeasurable (fun s : Fv F v => m (hermScal (Fv F v) σ s) (latV b v)) lam := by
    have h1 : AEMeasurable (fun s : Fv F v => ENNReal.ofReal (m (hermScal (Fv F v) σ s) (latV b v)).toReal)
        (lam.restrict ({0}ᶜ : Set (Fv F v))) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hVm
    rw [hres] at h1
    refine h1.congr (Eventually.of_forall fun s => ?_)
    exact ENNReal.ofReal_toReal (hfin _).ne
  rw [integral_toReal hae (Eventually.of_forall fun s => hfin _), ← hmass]
  simp

end GlobalTheory.CompanionTheory.SW.StdLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemCongruenceSubgroupOfDiv
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel Topology MatrixGroups

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_congruenceSubgroup_of_div {c : ℕ} {g : GL (Fin n) F}
    (hg : Div (c + 1) ((g : Matrix (Fin n) (Fin n) F) - 1)) :
    g ∈ congruenceSubgroup F n (c + 1) := by
  choose y hy hgy using hg
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hent : ∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (c + 1) * y i j := fun i j => by
    rw [← hgy i j, Matrix.sub_apply]
  have hint : ∀ i j, g i j ∈ 𝒪[F] := fun i j => by
    have h1 : g i j = (uniformizer F : F) ^ (c + 1) * y i j +
        (1 : Matrix (Fin n) (Fin n) F) i j := by rw [← hent i j, sub_add_cancel]
    rw [h1]
    exact add_mem (mul_mem (pow_mem (uniformizer F).2 _) (hy i j)) (hone i j)
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, hint i j⟩
  have hres : (IsLocalRing.residue 𝒪[F]).mapMatrix A = 1 := by
    ext i j
    have hmem : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j =
          uniformizer F * (uniformizer F ^ c * ⟨y i j, hy i j⟩) := by
        apply Subtype.ext
        have h2 : (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
            (1 : Matrix (Fin n) (Fin n) F) i j := by
          rw [Matrix.one_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [AddSubgroupClass.coe_sub, h2, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
        change g i j - _ = _
        rw [hent i j]
        ring
      rw [h1]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (irreducible_uniformizer F).not_isUnit)
    have h3 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sub, sub_eq_zero] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    have h1 : IsLocalRing.residue 𝒪[F] A.det = 1 := by
      rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h2] at h1
    exact zero_ne_one h1
  rw [mem_congruenceSubgroup_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' A hdet, Units.ext rfl⟩, fun i j => ?_⟩
  rw [hent i j, map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hy i j))

theorem smooth_of_isSmooth {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (h : GlobalTheory.PRep.IsSmooth ρ) : Smooth ρ := fun u => by
  have h1 : {g : GL (Fin n) F | ρ g u = u} ∈ 𝓝 (1 : GL (Fin n) F) :=
    (h u).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 h1
  exact ⟨m, fun g hg => hm (congruenceSubgroup_antitone F n (Nat.le_succ m)
    (mem_congruenceSubgroup_of_div hg))⟩

theorem g3 : G3 := fun _ _ _ _ _ π w => smooth_of_isSmooth _ (π.isSmooth_locRep w)

end GlobalTheory.CompanionTheory.JSSmooth

end
end

