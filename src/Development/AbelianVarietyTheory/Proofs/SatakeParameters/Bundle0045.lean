module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockComplementIsSubAtEnlargement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.SubWp

theorem enl_loc_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    C.loc (twistM M χ) g =
      (C.inc.comp (Br.toLLK (D.nbr i w hw))) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (C.inc.comp (Br.toLLK (D.nbr i w hw))) := by
  refine Matrix.ext fun a b => ?_
  change C.inc ((D.nbr i w hw).toLL (((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i))) *
      C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)))
  rw [Br.toLLK_alg, Br.toLLK_alg, ← map_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.SubWp

open GlobalTheory.SubWp in
theorem GlobalTheory.subWp_sub : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → IsSubOfSums (matRep (C.loc (WpO D.nd i ρ π))) (fun (_ : Unit) s => C.loc (rTwO D.nd i r π) s) := by
  intro D i w hw C r ρ π ⟨e, he⟩
  set f : KK D.nd i →+* ↥C.LL.1 := C.inc.comp (Br.toLLK (D.nbr i w hw)) with hf
  let A : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _)
  let B : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap)
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hRA : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * A = A * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
    intro g
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe,
      LinearMap.inl_apply]
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp <;> rfl
  refine ⟨1, fun _ => (), (LinearMap.pi fun _ => Matrix.mulVecLin (A.map f)), ?_, ?_⟩
  · intro v v' h
    have h1 := congrArg (fun z => (B.map f).mulVec (z 0)) h
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hBA,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mulVec] at h1
    exact h1
  · intro g v
    funext a
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply]
    change (A.map f).mulVec ((C.loc (WpO D.nd i ρ π) g).mulVec v) = (C.loc (rTwO D.nd i r π) g).mulVec ((A.map f).mulVec v)
    rw [WpO, rTwO, enl_loc_eq, enl_loc_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← hf, ← Matrix.map_mul, ← Matrix.map_mul, hRA]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardSmallTwistedDualJumpsEqRankStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_filter_abs_le_jT2_eq_rank : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ), (∀ i, 0 ≤ P.v i) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s → ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  first | exact @GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | exact GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank | (intros; apply GlobalTheory.HTW.card_small_twistedDualJumps_eq_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
section
noncomputable section

namespace GlobalTheory.WordJumpsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTW

section Clauses

variable (D : D7)

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Clauses

section Constituent

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_toLL : Continuous (D.nbr i w hw).toLL :=
  continuous_subtype_val.comp (D.nbr i w hw).eO_cont

theorem continuous_toGlobal :
    Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
  continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : Br.loc D.nbr i w hw M g a b =
      (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) := rfl

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous (Br.loc D.nbr i w hw M) := by
  refine continuous_matrix fun a b => ?_
  simp only [loc_apply]
  exact (continuous_toLL D i w hw).comp
    ((hM.comp (continuous_toGlobal D i w hw)).matrix_elem a b)

theorem toLLK_toK (c : D.nd.O i) :
    Br.toLLK (D.nbr i w hw) (toK D.nd i c) = (D.nbr i w hw).toLL c :=
  Br.toLLK_alg (D.nbr i w hw) c

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

end Constituent

section At

variable (D : D7) (L : SizeData₂ D) (ε : ℤˣ) (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end At

end GlobalTheory.WordJumpsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.DpstMap

section Letter

variable {LL U D D' : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] [AddCommGroup D'] [Module LL D']
  (m : U →+* End LL D) (m' : U →+* End LL D') (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)

def letterLin (T : D →ₗ[LL] D') (hT : ∀ c, T ∘ₗ m c = m' c ∘ₗ T) : Letter m F τ →ₗ[F] Letter m' F τ :=
  Submodule.mapQ _ _ (T.baseChange F) (iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    refine Submodule.mem_iSup_of_mem c ⟨T.baseChange F y, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this])

end Letter

section Dmap

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')

def tensV : V ⊗[ℚ_[l]] Bst P →ₗ[LL] V' ⊗[ℚ_[l]] Bst P := AlgebraTensorModule.map f LinearMap.id

theorem tensV_onB (T : End ℚ_[l] (Bst P)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (onB P LL V T x) = onB P LL V' T (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tensV_stRep (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f (stRep P ρ g x) = stRep P ρ' g (tensV P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [tensV, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {ρ ρ' f}

theorem tensV_mem_Dpst (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    tensV P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hK⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← tensV_stRep P ρ ρ' f hf, hK g hg]⟩

def dmap (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : ↥(Dpst P ρ) →ₗ[LL] ↥(Dpst P ρ') :=
  (tensV P f).restrict (tensV_mem_Dpst P hf)

variable (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
include hf

theorem dmap_phiD (x : ↥(Dpst P ρ)) : dmap P hf (phiD P ρ x) = phiD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_monD (x : ↥(Dpst P ρ)) : dmap P hf (monD P ρ x) = monD P ρ' (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) : dmap P hf (actD P ρ g x) = actD P ρ' g (dmap P hf x) :=
  Subtype.ext (tensV_stRep P ρ ρ' f hf g x.1)

theorem dmap_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) : dmap P hf (mulD P ρ c x) = mulD P ρ' c (dmap P hf x) :=
  Subtype.ext (tensV_onB P f _ x.1)

theorem dmap_phiU_zpow [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (n : ℤ) (x : ↥(Dpst P ρ)) :
    dmap P hf (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) x) =
      ((phiU P ρ' ^ n : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf x) := by
  have hinv : ∀ y, dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y) =
      (((phiU P ρ')⁻¹ : (End LL ↥(Dpst P ρ'))ˣ) : End LL ↥(Dpst P ρ')) (dmap P hf y) := by
    intro y
    have h1 : phiD P ρ' (dmap P hf ((((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) y)) =
        dmap P hf y := by
      rw [← dmap_phiD, ← coe_phiU, ← End.mul_apply, Units.mul_inv]; rfl
    rw [← h1, ← coe_phiU, ← End.mul_apply, Units.inv_mul]; rfl
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, coe_phiU,
      coe_phiU, dmap_phiD]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, End.mul_apply, End.mul_apply, ih, hinv]

end Dmap

section Lin

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK K) V} {ρ' : Representation ↥LL.1 ↥(GK K) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))

def wdLin : WDSpace P ι ρ →ₗ[ℂ] WDSpace P ι ρ' :=
  letI := algC ι LL
  letterLin (mulD P ρ) (mulD P ρ') ℂ (urC ι) (dmap P hf) fun c => LinearMap.ext fun x => dmap_mulD P hf c x

@[simp] theorem wdLin_mk (x : ↥(Dpst P ρ)) : wdLin P ι hf (wdMk P ι ρ x) = wdMk P ι ρ' (dmap P hf x) := rfl

theorem wdLin_wdN (y : WDSpace P ι ρ) : wdLin P ι hf (wdN P ι ρ y) = wdN P ι ρ' (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdN P ι ρ) = (wdN P ι ρ').comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdN_mk, wdLin_mk, dmap_monD]
  exact LinearMap.congr_fun this y

end Lin

section Weil

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
  {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
  (hf : ∀ g v, f (ρ g v) = ρ' g (f v))
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]

theorem dmap_weilD (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    dmap P hf (weilD Bw h P ρ σ x) = weilD Bw h P ρ' σ (dmap P hf x) := by
  rw [weilD_apply, weilD_apply]
  exact (dmap_actD P hf _ _).trans (congrArg _ (dmap_phiU_zpow P hf _ x))

theorem wdLin_wdRho (σ : ↥(Weil h)) (y : WDSpace P ι ρ) :
    wdLin P ι hf (wdRho P ι Bw h hj ρ σ y) = wdRho P ι Bw h hj ρ' σ (wdLin P ι hf y) := by
  have : (wdLin P ι hf).comp (wdRho P ι Bw h hj ρ σ) = (wdRho P ι Bw h hj ρ' σ).comp (wdLin P ι hf) :=
    LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, wdLin_mk, dmap_weilD]
  exact LinearMap.congr_fun this y

end Weil

section Charpoly

theorem charpoly_dvd_of_surjective {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup M'] [Module K M'] [FiniteDimensional K M'] (F : M →ₗ[K] M') (hF : Function.Surjective F)
    (T : Module.End K M) (T' : Module.End K M') (hT : ∀ x, F (T x) = T' (F x)) :
    T'.charpoly ∣ T.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker F, T x ∈ LinearMap.ker F := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [hT, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker F) T hA]
  refine Dvd.intro_left (T.restrict hA).charpoly ?_
  let e := F.quotKerEquivOfSurjective hF
  have he : (LinearMap.ker F).mapQ (LinearMap.ker F) T (fun x hx => hA x hx) = e.symm.conj T' := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
    apply e.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, hT]
    rfl
  rw [he, LinearEquiv.charpoly_conj]

theorem isNilpotent_zpow_sub_one {R : Type} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1)) (n : ℤ) :
    IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
  have hnat : ∀ k : ℕ, IsNilpotent ((u : R) ^ k - 1) := fun k => by
    rw [← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun i _ =>
      ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact hnat k
  · rw [zpow_negSucc]
    have e : (((u ^ (k + 1))⁻¹ : Rˣ) : R) - 1 = (((u ^ (k + 1))⁻¹ : Rˣ) : R) * -(((u : R) ^ (k + 1)) - 1) := by
      rw [mul_neg, mul_sub, mul_one, ← Units.val_pow_eq_pow_val, Units.inv_mul]; abel
    rw [e]
    refine Commute.isNilpotent_mul_left ?_ (hnat (k + 1)).neg
    refine Commute.neg_right ?_
    rw [← Units.val_pow_eq_pow_val]
    exact (Commute.units_inv_left (Commute.refl _)).sub_right (Commute.one_right _)

theorem commute_isNilpotent_of_unipotent {R : Type} [Ring R] {a b : R} (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (n : ℤ) (hc : Commute (u : R) b) (hb : b = a * ((u ^ n : Rˣ) : R)) : Commute a b ∧ IsNilpotent (b - a) := by
  have hUb : Commute ((u ^ n : Rˣ) : R) b := hc.units_zpow_left n
  have ha : a = b * (((u ^ n)⁻¹ : Rˣ) : R) := by rw [hb, mul_assoc, Units.mul_inv, mul_one]
  have haU : Commute a ((u ^ n : Rˣ) : R) := by
    rw [ha]
    exact hUb.symm.mul_left (Commute.units_inv_left (Commute.refl _))
  refine ⟨?_, ?_⟩
  · rw [hb]; exact (Commute.refl a).mul_right haU
  · have e : b - a = a * (((u ^ n : Rˣ) : R) - 1) := by rw [hb, mul_sub, mul_one]
    rw [e]
    exact Commute.isNilpotent_mul_left (haU.sub_right (Commute.one_right _)) (isNilpotent_zpow_sub_one u hu n)

end Charpoly

section Semisimple

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

theorem charpoly_wdRep (σ : ↥(Weil h)) :
    ((wdRep P ι Bw h hj ρ).ρ σ).charpoly = (wdRho P ι Bw h hj ρ σ).charpoly := by
  obtain ⟨u, -, hu, -, hcomm, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  obtain ⟨h1, h2⟩ := commute_isNilpotent_of_unipotent u hu (deg σ) (hcomm σ) (hρ σ)
  exact GlobalTheory.WeilDeligne.charpoly_eq_of_isNilpotent_sub h1 h2

theorem charPol_wdPst [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) (σ : ↥(Weil h)) :
    WD.charPol (wdPst P ι Bw h hj ρ) σ = (wdRho P ι Bw h hj ρ σ).charpoly := by
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk, charpoly_wdRep]

end Semisimple

end GlobalTheory.Pst.DpstMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.LocalFrobeniusOrbit

theorem norm_algHom_eq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} [Fact l.Prime]
    (c ρ : E →+* PadicAlgCl l) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ρ x = c (g x) := by
  let Φ : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] PadicAlgCl l) := fun g => c.toRatAlgHom.comp g.toAlgHom
  have hinj : Function.Injective Φ := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hgh
    exact c.injective this
  have hcard : Nat.card (E →ₐ[ℚ] PadicAlgCl l) ≤ Nat.card (E ≃ₐ[ℚ] E) := by
    rw [Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨g, hg⟩ := hbij.2 ρ.toRatAlgHom
  exact ⟨g, fun x => (congrArg (fun f : E →ₐ[ℚ] PadicAlgCl l => f x) hg).symm⟩

theorem embeddings_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  intro R H l _ h2 hq hd c K hc hcl P _ _ s hs
  haveI hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hN0 : ¬ l ∣ H.condN := by
    rw [H.dvd_condN_iff_small Fact.out]; tauto
  have hF := H.der.frob l hN0
  have hco : Nat.Coprime l H.condN := (Fact.out : l.Prime).coprime_iff_not_dvd.2 hN0
  obtain ⟨v, hvl, hv⟩ := _root_.GlobalTheory.LocPlace.exists_place_of_emb l H.E c
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI := v.isPrime
  haveI hvo : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hvl)
  have hsv : IsArithFrobAt ℤ s v.asIdeal := (H.frob_iff l hco v.asIdeal s).2 ((H.frob_iff l hco P s).1 hs)
  have hstab : MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) v.asIdeal = Subgroup.zpowers s := by
    refine le_antisymm (fun σ hσ => ?_) (Subgroup.zpowers_le.2 hsv.mem_stabilizer)
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul l v.asIdeal s σ hsv hσ
    rw [((hF v.asIdeal).2.2.2 ρ).1 hρ, one_mul]
    exact Subgroup.npow_mem_zpowers s k
  have hord : orderOf s = orderOf (H.galE s) :=
    (H.gal.orderOf_eq s).symm
  set N := orderOf (H.galE s) with hN
  have hNpos : 0 < N := hord ▸ orderOf_pos s
  haveI : NeZero N := ⟨hNpos.ne'⟩
  refine ⟨?_, ?_⟩
  · have hK : K.1 = IntermediateField.adjoin ℚ_[l] (Set.range c) := _root_.GlobalTheory.padicAlgCl_finite_dense_eq_adjoin l H.E c K.1 hc K.2 hcl
    have hdeg := _root_.GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer l H.E c v hv
    rw [← hord, ← Nat.card_zpowers, ← hstab, ← hdeg, hK]
  · intro τ
    let ρ : H.E →+* PadicAlgCl l := (τ : ↥K.1 →+* PadicAlgCl l).comp (c.codRestrict K.1 hc)
    obtain ⟨g, hg⟩ := exists_aut_comp c ρ
    have hρx : ∀ x, ρ x = τ ⟨c x, hc x⟩ := fun x => rfl
    have hgs : g ∈ Subgroup.zpowers s := by
      rw [← hstab]
      refine Formalism.FrobeniusOrbits.Decomp.mem_stab_of g v.asIdeal (fun z => ?_)
      rw [hv, hv]
      have h1 : c ((g • z : 𝓞 H.E) : H.E) = τ ⟨c z, hc z⟩ := by
        rw [← hρx, hg]; rfl
      rw [h1, norm_algHom_eq]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgs
    have hpow : ∀ j : ZMod N, s ^ j.val = s ^ ((j.val : ℤ)) := fun j => (zpow_natCast s j.val).symm
    refine ⟨(k : ZMod N), fun x => ?_, fun j hj => ?_⟩
    · rw [← hρx, hg, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
    · have hgj : g = s ^ j.val := by
        refine AlgEquiv.ext fun x => c.injective ?_
        rw [← hg, hρx, hj]
      apply ZMod.val_injective
      have h3 : s ^ j.val = s ^ (k : ZMod N).val := by
        rw [← hgj, hpow, ZMod.val_intCast, ← hord, zpow_mod_orderOf, hk]
      have h4 := pow_inj_mod.1 h3
      rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt j), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h4
      exact h4

end GlobalTheory.LocalFrobeniusOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtensionStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpannedByRepMatrices_of_scalarExtension : ∀ {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L)), EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L)))) → EndSpanned τ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_endSpanned_map | exact GlobalTheory.SplitField.endSpanned_of_endSpanned_map | (intros; apply GlobalTheory.SplitField.endSpanned_of_endSpanned_map <;> assumption)
end

