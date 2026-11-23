module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HatOfInvariantSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.TwoMaps

theorem toHatS_eq_of_hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → toHatS O K l e f = x := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f x hfx
  let fR : Rpi O K l e := ⟨(f : K⟦X⟧), invL_S_le_Rpi l e f.2⟩
  have h0 : hat O l e (fR : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHat O K l e fR) := hat_coe_Rpi l e fR
  have h1 : toHatS O K l e f = toHat O K l e fR := rfl
  have h2 : hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHatS O K l e f) := by
    rw [h1]; exact h0
  rw [h2] at hfx
  have hE0 : EIn l e (invL l (A O K)) ≠ 0 := fun h => by
    have h3 : E K l e = 0 := congrArg Subtype.val h
    exact (isUnit_E (K := K) l e).ne_zero h3
  have hreg : ∀ y : Ahat O K l e, Ehat O K l e * y = 0 → y = 0 := fun y hy =>
    GlobalTheory.MemLoc.FilPrincipal.regular_of_isDomain rfl hE0 y hy
  have hmem : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro y hy <;> apply hreg <;> first | exact hy | (rw [mul_comm]; exact hy)
  have hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
    IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) (AhatE O K l e) (Submonoid.powers_le.2 hmem)
  exact hinj hfx

theorem iSD_eq_of_mem_invL_A : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)), (f : K⟦X⟧) ∈ invL l (A O K) → ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f hf
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]

theorem iSD_eq_iHat_of_hat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K], ∀ (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → ϖ.iSD O K f = ϖ.iHat O K x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ f x hfx
  obtain rfl := toHatS_eq_of_hat l e O K ϖ f x hfx
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ

  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
    fun s => ϖ.iSD_of_mem O K s.2 _
  have key : ∀ s : S O K e, crisToOD l O (ϖ.iS O K s) =
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
    intro s
    rw [← sub_eq_zero]
    set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
    have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
      simp only [hD, map_add (f := _)]; ring
    have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
      simp only [hD, map_mul, map_pow, map_natCast]; ring
    have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
      intro m
      obtain ⟨N, hN⟩ := _root_.GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
      have hw : ∀ k : ℕ, ∃ y : OA l O, ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
        intro k
        obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
        obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
        set hS' : S O K e := ⟨h, hh⟩
        have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
          sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
        set P : S O K e := ⟨_, hP⟩
        have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
        have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
          have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
            simp only [P]; linear_combination hs
          rw [this]
          exact sum_mem fun n _ => monomial_mem_invL l n _
        have hDP : D P = 0 := by
          simp only [hD, sub_eq_zero]
          rw [← hS]
          exact iSD_eq_of_mem_invL_A l e O K ϖ _ hPA
        obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
        obtain ⟨y2, hy2⟩ := _root_.GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
        refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
        have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
            (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') - toOD l O y1) -
              (l : OD l O) ^ N * ((l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
          rw [hsP, hDadd, hDP, zero_add, hDmul]
          simp only [hD, map_sub, map_mul, map_pow, map_natCast]
          ring
        rw [e1]
        exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
      have h1 := _root_.GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
      rw [pow_add, mul_assoc] at h1
      exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
    have hc := ϖ.complete_OD O K
    exact hc.toIsHausdorff.haus' _ fun n => by
      simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
      exact Ideal.mem_span_singleton.2 (hdiv n)
  have hext : ϖ.iSD O K = (ϖ.iHat O K).toRingHom.comp (toHatS O K l e) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact (hS s).trans (key s))
  exact RingHom.congr_fun hext f

end GlobalTheory.BKReal.TwoMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatStab

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hx' : x = ∑ i ∈ (b.repr x).support, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have h0 := linearIndependent_iff'.1 hli _ _ hx
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ (b.repr x).support
  · simpa using h0 i hi
  · simpa using Finsupp.notMem_support_iff.1 hi

theorem latStable_of_latInt : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  intro D M B j h1 h2 w hI v k hvk x hx
  classical
  obtain ⟨s, ϖ, hcj, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
  have hinj := jMt_injective D (D.what₂.muTw w) j
  let f : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.MtL (D.what₂.muTw w) j := fun g =>
    if h : g ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j) then h.choose else 0
  have hf : ∀ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.jMt (D.what₂.muTw w) j (f g) = g := by
    intro g hg
    have h := hI.1 g hg
    simp only [f, dif_pos h]
    exact h.choose_spec
  have key : ∀ y ∈ genSet D (D.what₂.muTw w) j, B.hK j w v k (B.iV j w y) ∈ latLoc B j w := by
    intro y hy
    obtain ⟨c, hc0, hcE⟩ := hI.2 v k s ϖ hvk hcj hu _ hy
    have e1 := B.hL_def j w h1 h2 v k s ϖ hvk hcj hu y
    rw [hcE] at e1
    have e2 := (M (D.what₂.muTw w) j h1 h2).real_inj e1
    have e3 : B.hL j w v k y = ∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, c g • f g := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e2, map_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smulₛₗ, hf g hg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [B.hK_def, e3, map_sum]
    refine Submodule.sum_mem _ fun g hg => ?_
    rw [map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w j w (c g)).1 (hc0 g)
    rw [← ho, algebraMap_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f g, ?_, rfl⟩)
    show D.what₂.jMt (D.what₂.muTw w) j (f g) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen
    rw [hf g hg]; exact hg
  have hle : latLoc B j w ≤ (latLoc B j w).comap ((B.hK j w v k).restrictScalars (B.Oc j w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  exact hle hx

end GlobalTheory.LatStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem bot_emb_factor {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (hL : LL.1 ≤ LL'.1)
    (τ' : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL'.1) :
    ∃ τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1, τ' = (incl hL).comp τ := by
  refine ⟨IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ_[l] _) ≤ LL.1), ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 (show x.1 ∈ (⊥ : IntermediateField ℚ_[l] _) from x.2)
  have hx : x = algebraMap ℚ_[l] _ c := Subtype.ext hc.symm
  rw [hx, AlgHom.commutes, AlgHom.commutes]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jumpsInV_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb U H τ' a ha
  obtain ⟨τ, rfl⟩ := bot_emb_factor hL τ'
  refine H τ a ?_
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr (pc Pl h hN hF hS).PD b.equivFun
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf_equiv b T.ρ) τ a
  have e2 := Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general (pc Pl h hN hF hS).PD (incl hL)
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf b T.ρ) τ a
  exact e1.2 (e2.2 ha)

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostFieldImageMemUnramifiedAdjoinRootsOfUnity
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

noncomputable section

namespace GlobalTheory.HostImage

theorem host_image_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  intro D i w hw x
  have h := UpperTheory.Small.factorization_condN_le D.host (D.nd.lPrime i).out
  refine UpperTheory.Small.image_mem_Kur_sup D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) ?_ x
  by_cases h2 : D.nd.l i = 2
  · rw [D.nd.restNLevelExponent_of_two i h2, ← h2]
    exact h.2 h2
  · rw [D.nd.restNLevelExponent_of_odd i h2]
    exact h.1

end GlobalTheory.HostImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section General

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] [NeZero a]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_Ehat_pow_mul (w : ZMod a → ι → AhatE O K l e) :
    ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * w τ i := by
  classical
  choose r z hz using fun p : ZMod a × ι => IsLocalization.Away.surj (Ehat O K l e) (w p.1 p.2)
  refine ⟨Finset.univ.sup r, fun τ i => Ehat O K l e ^ (Finset.univ.sup r - r (τ, i)) * z (τ, i),
    fun τ i => ?_⟩
  have hle : r (τ, i) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
  rw [map_mul, map_pow, ← hz (τ, i), mul_left_comm, ← pow_add, Nat.sub_add_cancel hle, mul_comm]

end General

theorem hsum_mul_Ehat_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P n s m
  exact exists_Ehat_pow_mul (GlobalTheory.BKGal.JumpDR.hsum P s fun k => (m k).1)

end GlobalTheory.BKGal.JumpDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image : ∀ {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K), e * e = e → e.rank = t → ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧ ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  first | exact @GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | exact GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | (intros; apply GlobalTheory.BlockCharpoly.blockPol_eq_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.AdmHerrLocal

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F :=
  fun D HW F => Formalism.MainNotions.HerrComplexNaturality.herr_class_maps_of_naturality D HW F
    (Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_a_and_natural D HW F))
    (GlobalTheory.HerrExtUnit.main D HW F)

end GlobalTheory.AdmHerrLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InerDecomp
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section
namespace GlobalTheory.InertiaDecomp
open Pointwise

theorem iner_decomp : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (g : ↥(GK K)), g ∈ (pc P h hN hF hS).Iner → ∃ s : ↥(GK K), s ∈ IK K ∧ s⁻¹ * g ∈ GKin h := by
  intro l _ P K K' h hN hF hS g hg
  haveI : Nontrivial P.R.B := by
    by_contra hB
    have : Subsingleton P.R.B := not_nontrivial_iff_subsingleton.mp hB
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact Submodule.zero_mem _

  have hfix : ∀ x ∈ K0 K', (g : GQ l) x = x := by
    intro x hx
    have h1 : (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩) = algebraMap ↥(K0 K') P.R.B ⟨x, hx⟩ :=
      hg ⟨x, hx⟩
    rw [P.PD_actB] at h1
    have h2 := P.actQ_Kur ((g : ↥(GK K)) : GQ l) ⟨x, hx.2⟩ ⟨_, GlobalTheory.TameInertiaCyclic.map_mem_Kur _ hx.2⟩ rfl
    have h3 := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (h2.symm.trans h1)
    exact congrArg Subtype.val h3
  haveI := K'.2

  let S : Subgroup (GQ l) := (MaximalUnramifiedExtension l).fixingSubgroup ⊔ (K'.1).fixingSubgroup
  have hSo : IsOpen (S : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_right (IntermediateField.fixingSubgroup_isOpen K'.1)
  let SC : ClosedSubgroup (GQ l) := ⟨S, Subgroup.isClosed_of_isOpen S hSo⟩
  have hfe : IntermediateField.fixedField (SC : Subgroup (GQ l)) ≤ K0 K' := by
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    refine IntermediateField.mem_inf.2 ⟨?_, ?_⟩
    · exact (InfiniteGalois.fixedField_fixingSubgroup K'.1).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_right hf))
    · exact (InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)).le
        ((IntermediateField.mem_fixedField_iff _ _).2 fun f hf => hx f (Subgroup.mem_sup_left hf))
  have hgS : (g : GQ l) ∈ S := by
    have e := InfiniteGalois.fixingSubgroup_fixedField SC
    have : (g : GQ l) ∈ (IntermediateField.fixedField (SC : Subgroup (GQ l))).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact hfix x (hfe hx)
    rw [e] at this
    exact this
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  have hgS' : (g : GQ l) ∈ ((MaximalUnramifiedExtension l).fixingSubgroup : Set (GQ l)) * ((K'.1).fixingSubgroup : Set (GQ l)) := by
    rw [← Subgroup.normal_mul]; exact hgS
  obtain ⟨b, hb, a, ha, hba⟩ := hgS'
  have haK : a ∈ GK K := GK_le h ha
  have hbK : b ∈ GK K := by
    have : b = (g : GQ l) * a⁻¹ := by rw [← hba, mul_inv_cancel_right]
    rw [this]; exact mul_mem g.2 (inv_mem haK)
  refine ⟨⟨b, hbK⟩, Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hb x hx, ?_⟩
  rw [GKin, Subgroup.mem_subgroupOf]
  have : (((⟨b, hbK⟩ : ↥(GK K))⁻¹ * g : ↥(GK K)) : GQ l) = a := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hba]; simp
  rw [this]; exact ha

end GlobalTheory.InertiaDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem char_inertia_trivial_on_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l)
    (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) →
    ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)),
      (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  intro l _ LL χ hopen
  obtain ⟨t₁, ht₁, ht₁e⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨t₂, ht₂, ht₂e⟩ := isOpen_induced_iff.mp ht₁
  have h1 : (1 : GQ l) ∈ t₂ := by
    have hk : (1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := χ.ker.one_mem
    rw [← ht₁e] at hk
    have hk' : ((1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) ∈ t₁ := hk
    rw [← ht₂e] at hk'
    exact hk'
  obtain ⟨E, hfd, hN, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) t₂).1 (ht₂.mem_nhds h1)
  refine ⟨⟨E, hfd⟩, hN, fun g hg => ?_⟩
  have hg₂ : ((g : Gl l) : GQ l) ∈ t₂ :=
    hE ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hg x hx)
  have hg₁ : (g : Gl l) ∈ t₁ := by
    rw [← ht₂e]; exact hg₂
  have hg₀ : g ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    rw [← ht₁e]; exact hg₁
  exact hg₀

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq
section
noncomputable section

namespace GlobalTheory.IneAway

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem placesOver_finite_of_prime (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

theorem isoLoc_cusp (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end GlobalTheory.IneAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  first | exact @GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | exact GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | (intros; apply GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat <;> assumption)
end

