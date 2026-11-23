module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBound
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isDualLat1_dual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) (GlobalTheory.Pass.LocDirect.latDual i w hw M hM) (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  intro D i w hw k M hM
  refine ⟨GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) (Br.loc D.nbr i w hw M) (dualMat i w hw M)
    (fun g => dualMat_apply i w hw M g), fun y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩ _ ⟨z', rfl⟩
    exact ⟨_, GlobalTheory.BKLatticeCochain.incl_dot z' z⟩
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun a => ?_
    obtain ⟨o, ho⟩ := h (GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw))) ⟨_, rfl⟩
    refine ⟨o, ?_⟩
    rw [← ho]
    change GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw)) ⬝ᵥ
      (y : Fin k → Br.LL D.nbr i w hw) = y a
    simp [GlobalTheory.BKLatticeCochain.incl_apply, dotProduct, Pi.single_apply,
      apply_ite (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw))]
    exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ a))

theorem isCrys_dual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.Udual i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hF i w hw k M hM K' h hcrys
  haveI := isTopRing i w hw
  have hi : Continuous (Subgroup.inclusion (GK_le h)) := continuous_subtype_val.subtype_mk _
  have hU : Continuous ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM).comp hi
  have hU' : Continuous ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (continuous_dualMat i w hw M hM).comp hi
  have hc : ∀ g : ↥(GK K'), ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)
        (Subgroup.inclusion (GK_le h) g) : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    intro g
    simp only [cycLL, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    congr 1
    rw [(D.loc (D.nd.l i)).PD_χ, Br.PD, (D.loc (D.nd.l i)).PD_χ]
    rfl
  have hd : IsDual1 ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (matRep ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
    refine GlobalTheory.PotDual.isDual1_of_eq _ _ _ fun g => ?_
    rw [hc]
    rfl
  exact (hF (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU)
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU') _ hd hcrys

theorem finrank_H1fT_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL] (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ), (∀ y : G → A.V, Continuous y → ∃ m : O, m ≠ 0 ∧ ∀ g, m • y g ∈ L.T) → finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD A.ρ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ _ A L hT
  have h := GlobalTheory.BlochKatoRank.rank_subquotient_eq (O := O) (K := LL) (X := G → A.V) (Y := G → A.V)
    LinearMap.id (latticeCocycles L) (latticeCoboundaries L) (latticeFiniteCocycles PD L) (finiteCocycles PD A.ρ) (Formalism.WeaklyAdmissibleFiltrations.B1 A.ρ)
    (fun a ha => ha.2) ?_ ?_ ?_
  · exact congrArg Cardinal.toNat h
  · rintro b ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, rfl⟩
    obtain ⟨m, hm, hx⟩ := hT (fun _ => x) continuous_const
    refine ⟨m, hm, m • x, hx Classical.ofNonempty, ?_⟩
    change cob A.ρ (m • x) = m • cob A.ρ x
    exact LinearMap.map_smul_of_tower _ _ _
  · intro y hy
    obtain ⟨m, hm, hy'⟩ := hT y hy.1.1
    have hZ : m • y ∈ latticeCocycles L :=
      ⟨(continuousCocycles A.ρ).smul_of_tower_mem m hy.1, Submodule.mem_pi.2 fun g _ => hy' g⟩
    exact ⟨m, hm, m • y, hZ, ⟨hZ, (finiteCocycles PD A.ρ).smul_of_tower_mem m hy⟩, rfl⟩

theorem latDual_bounded {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) (y : Br.G D.nbr i w hw → (Udual i w hw M hM).V) (hy : Continuous y) :
    ∃ m : Br.OLL D.nbr i w hw, m ≠ 0 ∧ ∀ g, m • y g ∈ (latDual i w hw M hM).T := by
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  obtain ⟨N, hN⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL (D.nbr i w hw).LL
    (m := k) y hy
  refine ⟨(D.nd.l i : Br.OLL D.nbr i w hw) ^ N, ?_, fun g => ?_⟩
  · intro h0
    have := congrArg (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) h0
    rw [map_pow, map_natCast, map_zero] at this
    exact (Fact.out : (D.nd.l i).Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun j => ⟨⟨_, hN g j⟩, ?_⟩
    change _ = ((D.nd.l i : Br.OLL D.nbr i w hw) ^ N) • (y g : Fin k → Br.LL D.nbr i w hw) j
    rw [Algebra.smul_def, map_pow, map_natCast]
    rfl

theorem dualLat_rank : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  intro D hF hBK hPDR i w hw hdeg k M hM K' h hcrys
  refine ⟨Udual i w hw M hM, latDual i w hw M hM, dotProductBilin _ _, isDualLat1_dual D i w hw M hM, ?_⟩
  have hcrys' := isCrys_dual D hF i w hw M hM K' h hcrys
  have hdR : IsDR (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM).ρ :=
    hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h (Udual i w hw M hM) hcrys'
  have hle := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw
    (D.nbr i w hw).LL hdeg (hBK (D.nd.l i) _) (Udual i w hw M hM) hdR
  haveI : IsFractionRing (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) :=
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).1.2.2
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  rw [finrank_H1fT_eq (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM) (latDual i w hw M hM) (latDual_bounded i w hw M hM)]
  refine hle.trans (le_of_eq ?_)
  exact Module.finrank_fin_fun _

end GlobalTheory.Pass.LocDirect

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSub
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.CrPer

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem eq_const_add_X_mul (bk : BK K) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1)
    (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ) (hκ : IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ) (x : bk.DS ρ) :
    ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul l K bk ρ h0 h1 κ hκ x

theorem isDiscMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'} {u'' : A''}
    {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {F' : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hF' : IsDiscMap (l := _) (u := _) (ρ := _) f' F') :
    IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  ⟨fun a => by simp [hF.ext, hF'.ext], fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem dvd_gal_sub (bk : BK K) (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G)
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i) (x : bk.DS bk.ρ₀) :
    bk.iS X ∣ G (i x) - i x := by
  obtain ⟨hmap, -, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨κ, hκ⟩ := hmap (Wq l bk.a) bk.S C 0 X 1 bk.ρ₀ 0 hρ0 (by simp) (by simp)
  obtain ⟨c, x₁, rfl⟩ := eq_const_add_X_mul bk bk.ρ₀ hρ0 hρ1 κ hκ x
  have hc : G (i (κ c)) = i (κ c) := by
    have h1 : IsDiscMap (l := _) (u := _) (ρ := _) ((Per.σA (g : GQ l)).comp (bk.ev.comp C)) ((G.comp i).comp κ) :=
      isDiscMap_comp hκ (isDiscMap_comp hi hG)
    have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp C) (i.comp κ) := isDiscMap_comp hκ hi
    have e : (Per.σA (g : GQ l)).comp (bk.ev.comp C) = bk.ev.comp C :=
      RingHom.ext fun w => by simp [bk.ev_C, bk.gal_w]
    rw [e] at h1
    exact RingHom.congr_fun (h1.unique h2) c
  obtain ⟨w, hw⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  have hX : i (toDisc l (X : bk.S) bk.ρ₀ X) = bk.iS X := hi.ext X
  have hGX : G (bk.iS X) = bk.iS X * bk.iA w := by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)) = _
    rw [hG.ext, hw, map_mul]; rfl
  rw [map_add i, map_mul i, hX, map_add G, map_mul G, hc, hGX]
  exact ⟨bk.iA w * G (i x₁) - i x₁, by ring⟩

end GlobalTheory.BKLim.CrPer


open GlobalTheory.BKLim.CrPer in
theorem GlobalTheory.BKLim.Frame.isCr_of_wSeed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  intro l _ K bk τ _ d ρ _ s N F Y Z _ hZ _ hG hκ g i j
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨Gm, hGm⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
  obtain ⟨im, him⟩ := hmap bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by simp) (by simp)
  have key := hG g Gm im hGm him
  rw [hκ g, one_mul] at key
  set q := Ideal.Quotient.mk (Ideal.span {bk.iS X}) with hqdef
  have hq : ∀ x, q (Gm (im x)) = q (im x) := fun x =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (dvd_gal_sub bk _ Gm hGm im him x))
  have hqS : ∀ a : bk.S, q (Gm (bk.iS a)) = q (bk.iS a) := fun a => by
    have h := hq (toDisc l (X : bk.S) bk.ρ₀ a)
    rwa [him.ext] at h
  have hl : IsUnit ((l : bk.DA bk.ρ₀)) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hu0 : q (bk.iS X) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hE : IsUnit (q (bk.iS bk.E)) := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have e1 : bk.E = X * PowerSeries.mk (fun p => coeff (p + 1) bk.E) + C ((l : Wq l bk.a) * w) := by
      conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
      rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
    rw [e1]
    simp only [map_add (f := _), map_mul, map_natCast, hu0, zero_mul, zero_add]
    exact (hl.map q).mul ((w.isUnit.map (C : Wq l bk.a →+* bk.S)).map (q.comp bk.iS))
  have hsm : ∀ (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), (c • M).map q = q c • M.map q :=
    fun c M => by ext a b; simp
  set P := s.X.map bk.iS * Z.map im with hPdef
  have hPG : (P.map Gm).map q = P.map q := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hPdef, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, hq, hqS]
  have hPu : IsUnit (P.map q) := by
    rw [hPdef, Matrix.map_mul]
    refine IsUnit.mul ?_ ?_
    · have e : (s.X.map bk.iS).map q = (q.comp bk.iS).mapMatrix s.X := by ext; rfl
      rw [e, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
      have hd := congrArg Matrix.det s.X_mul
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
      have h2 : IsUnit ((q.comp bk.iS) (s.X.det * s.X'.det)) := by
        rw [hd]
        simp only [map_pow, map_mul, map_natCast, RingHom.comp_apply]
        exact ((((hl.map q).pow _).mul (hE.pow _)).pow _)
      rw [map_mul] at h2
      exact isUnit_of_mul_isUnit_left h2
    · have e : (Z.map im).map q = (q.comp im).mapMatrix Z := by ext; rfl
      rw [e]
      exact hZ.map _
  have k2 := congrArg (fun M => Matrix.map M q) key
  simp only [hsm, Matrix.map_mul, hqS] at k2
  rw [hPG] at k2
  simp only [map_pow, hqS] at k2
  have k3 : q (bk.iS bk.E) ^ s.N • (P.map q * (((F.ε g).map bk.iA).map q - 1)) = 0 := by
    rw [mul_sub, mul_one, smul_sub, k2, sub_self]
  rw [(hE.pow _).smul_eq_zero, hPu.mul_right_eq_zero, sub_eq_zero] at k3
  have k5 : q (bk.iA ((F.ε g - 1) i j)) = 0 := by
    have h := congrFun (congrFun k3 i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> simp [h]
  exact (_root_.GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk _).2 (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 k5))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproduct
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem ringHom_map_sum' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {ι : Type} (s : Finset ι)
    (g : ι → A) : f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s


set_option maxHeartbeats 400000 in
theorem dvd_l_of_sections_env_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hrel hsec j
  have hfr : IsFrame bk (ainfObj K) (bk.ev bk.E) (bk.ev X) := by
    have := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk (ainfObj K) bk.ι
    rwa [show BK.hf bk.ι = bk.ev from rfl] at this
  have hAn := _root_.GlobalTheory.BSP.nonempty_env l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) hfr
  obtain ⟨An⟩ := hAn
  obtain ⟨q, ⟨hq1, hq2⟩, -⟩ := En.univ An.Q (An.inl.comp bk.ι) An.inr
  have hE : q.f (BK.hf En.inl bk.E) = An.inl.f (bk.ev bk.E) := by
    change (q.comp En.inl).f bk.E = _
    rw [hq1]; rfl
  have hrel' : ∀ j, An.inl.f (bk.ev bk.E) ^ h * q.f (x j) = ∑ i, An.Q.D.φ (q.f (x i)) * q.f (c i j) := by
    intro j
    have t1 : q.f (BK.hf En.inl bk.E ^ h * x j) = q.f (BK.hf En.inl bk.E ^ h) * q.f (x j) := q.f.map_mul _ _
    have t2 : q.f (BK.hf En.inl bk.E ^ h) = An.inl.f (bk.ev bk.E) ^ h := (q.f.map_pow _ _).trans (congrArg (· ^ h) hE)
    have t3 : q.f (BK.hf En.inl bk.E ^ h * x j) = An.inl.f (bk.ev bk.E) ^ h * q.f (x j) :=
      t1.trans (congrArg (fun t : An.Q.A => t * q.f (x j)) t2)
    have e2a := ringHom_map_sum' q.f Finset.univ (fun i => En.Q.D.φ (x i) * c i j)
    have e2b : ∀ i, q.f (En.Q.D.φ (x i) * c i j) = An.Q.D.φ (q.f (x i)) * q.f (c i j) := fun i =>
      (q.f.map_mul _ _).trans (congrArg (fun t : An.Q.A => t * q.f (c i j)) (Hom.f_φ q (x i)))
    have e2c := Finset.sum_congr (s₁ := (Finset.univ : Finset κ)) rfl (fun i (_ : i ∈ Finset.univ) => e2b i)
    have e3 := congrArg q.f (hrel j)
    exact t3.symm.trans (e3.trans (e2a.trans e2c))
  have hsec' : ∀ (g : ↥(GK K)) (s : Hom An.Q (ainfObj K)), s.comp An.inl = Hom.id _ →
      s.comp An.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (q.f (x j)) := by
    intro g s hs1 hs2 j
    have h1 : (s.comp q).comp En.inl = bk.ι := by
      have : (s.comp q).comp En.inl = (s.comp An.inl).comp bk.ι := by
        rw [show (s.comp q).comp En.inl = s.comp (q.comp En.inl) from Hom.ext' rfl, hq1]
        exact Hom.ext' rfl
      rw [this, hs1]; exact Hom.ext' rfl
    have h2 : (s.comp q).comp En.inr = (ainfHom K g).comp bk.ι := by
      rw [show (s.comp q).comp En.inr = s.comp (q.comp En.inr) from Hom.ext' rfl, hq2, hs2]
    exact hsec g (s.comp q) h1 h2 j
  have key := _root_.GlobalTheory.BSP.l_dvd_of_galois_sections l K bk An κ (fun i => q.f (x i)) (fun i k => q.f (c i k)) h hrel' hsec'
  exact _root_.GlobalTheory.BSP.envPush_dvd_l l K bk En An q hq1 hq2 (x j) (key j)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantLatticeMatrixOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.equivariant_matrix_over_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨X, hX, hfix, hphi⟩ := _root_.GlobalTheory.BSP.MReal.exists_fixed_frob l K bk d d' S S' ρ ρ' T T' hT hT' f hf
  have hOE := _root_.GlobalTheory.BSP.EquivOE.main l K bk d d' S S' X hfix hphi
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨M, x, hx⟩ := _root_.GlobalTheory.BSP.PoleBound.exists_pow_smul l K bk τ hτ d d' S S' ρ ρ' T T' hT hT' f X hX
  obtain ⟨Y, hY⟩ := _root_.GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d' M X x hOE hx
  exact ⟨Y, by rw [hY]; exact hX⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOne
section
noncomputable section

namespace GlobalTheory.JSW

open PowerSeries

theorem hasSum_coeff_mk_mul_polynomial (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (p : Polynomial ℂ) :
    HasSum (fun d => coeff d (mk c * (p : PowerSeries ℂ))) ((∑' d, c d) * p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [Polynomial.coe_add, mul_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    have hf : (fun d => coeff d (mk c * ((Polynomial.monomial n a : Polynomial ℂ) : PowerSeries ℂ)))
        = fun d => if n ≤ d then c (d - n) * a else 0 := by
      funext d
      rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow, ← mul_assoc,
        PowerSeries.coeff_mul_X_pow']
      split_ifs <;> simp [PowerSeries.coeff_mul_C]
    rw [hf, Polynomial.eval_monomial, one_pow, mul_one]
    refine (hasSum_nat_add_iff' n).mp ?_
    have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then c (i - n) * a else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp [not_le.mpr hi]
    rw [h0, sub_zero]
    simpa using (Summable.of_norm hc).hasSum.mul_right a

theorem eulerInverse_eval_one {ι : Type} [Fintype ι] (c : ℕ → ℂ) (hc : Summable fun d => ‖c d‖)
    (Q : ι → ℂ)
    (h : PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1) :
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  set P : Polynomial ℂ := ∏ p, (1 - Polynomial.C (Q p) * Polynomial.X) with hPdef
  have hP : (P : PowerSeries ℂ) = ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) := by
    have := map_prod (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
      (fun p => 1 - Polynomial.C (Q p) * Polynomial.X) Finset.univ
    rw [hPdef]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply] at this
    rw [this]
    simp
  have h1 := hasSum_coeff_mk_mul_polynomial c hc P
  rw [hP, h] at h1
  have h2 : HasSum (fun d => coeff d (1 : PowerSeries ℂ)) 1 := by
    simpa [PowerSeries.coeff_one] using hasSum_ite_eq 0 (1 : ℂ)
  have h3 := h1.unique h2
  have hev : P.eval 1 = ∏ p, (1 - Q p) := by simp [hPdef, Polynomial.eval_prod]
  rw [hev] at h3
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, mul_zero] at h3
    exact zero_ne_one h3
  · rw [← eq_inv_of_mul_eq_one_left h3]
    exact (Summable.of_norm hc).hasSum

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIso
section
open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeGal

def conjGal {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) :
    (Ω' ≃ₐ[E'] Ω') →* (Ω ≃ₐ[E] Ω) where
  toFun τ :=
    { toRingEquiv := (φ.trans τ.toRingEquiv).trans φ.symm
      commutes' := fun x => by
        show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hφ, AlgEquiv.commutes, ← hφ, RingEquiv.symm_apply_apply] }
  map_one' := by
    ext z
    show φ.symm (φ z) = z
    exact φ.symm_apply_apply z
  map_mul' τ τ' := by
    ext z
    show φ.symm ((τ * τ') (φ z)) = φ.symm (τ (φ (φ.symm (τ' (φ z)))))
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem conjGal_apply {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x))
    (τ : Ω' ≃ₐ[E'] Ω') (z : Ω) : conjGal φ j hφ τ z = φ.symm (τ (φ z)) := rfl

theorem exists_abHom_of_ringEquiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) →
    ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧
      ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) →
        ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ φ j hφ
  haveI : Algebra.IsIntegral E' Ω' := (IsAlgClosure.isAlgebraic (R := E') (K := Ω')).isIntegral
  haveI : IsClosed ((commutator (Formalism.ConjugateSelfDual.G E Ω)).topologicalClosure : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let c := conjGal φ j hφ
  have hc : Continuous c :=
    continuous_galHom_of_fix c fun y => ⟨φ y, fun τ hτ => by
      rw [conjGal_apply, hτ, RingEquiv.symm_apply_apply]⟩
  let r : Formalism.ConjugateSelfDual.G E' Ω' →* Gab E Ω := (toAb E Ω).comp c
  have hr : Continuous r := QuotientGroup.continuous_mk.comp hc
  refine ⟨liftAb r hr, continuous_liftAb r hr, fun τ σ h => ?_⟩
  rw [liftAb_toAb]
  show toAb E Ω (c τ) = toAb E Ω σ
  congr 1
  ext z
  rw [conjGal_apply, ← h, RingEquiv.symm_apply_apply]

end GlobalTheory.HeckeGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStepStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phiContraction_disc_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  first | exact @GlobalTheory.BSP.exists_discStep | exact GlobalTheory.BSP.exists_discStep | (intros; apply GlobalTheory.BSP.exists_discStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncLog_gal_mod_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(GK K) → ℤ_[l]),
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) →
    ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K),
      aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l ((bk.Ep.natDegree : ℤ_[l]) * c g)) * C.j C.t) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (exact GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil) | (intros; apply GlobalTheory.BSP.BK.exists_truncLog_gal_mod_fil  <;> assumption)
end

