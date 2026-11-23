module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRham
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.SummandDualDR


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  intro D hFont hP i r hr Xs w hw n hPot X hX X' PX hD
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hx⟩ := hPot
  obtain ⟨a, x, j, hjinj, hjeq, -⟩ := hX
  obtain ⟨h1, h2, h3, h4⟩ := hD
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
  let W : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X.V, ρ := X.ρ.comp incl, cont := fun v => (X.cont v).comp hincl }
  let W' : GRep ↥(GK K') ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
    { V := X'.V, ρ := X'.ρ.comp incl, cont := fun v => (X'.cont v).comp hincl }
  let Ms' : ↥Xs → (↥(GK K') →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw)) :=
    fun y => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp incl
  have hc' : ∀ y v, Continuous fun g => (Ms' y g).mulVec v := fun y v =>
    ((GlobalTheory.JumpDual.loc_cont D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr y).1).comp hincl).matrix_mulVec
      continuous_const
  have hcr' : ∀ y, IsCrys ((D.loc (D.nd.l i)).PD K') (matRep (Ms' y)) := fun y =>
    (GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hx y).1
  have hsub : IsSubOfSums W.ρ (fun y => ⇑(Ms' y)) := by
    refine ⟨a, x, j, hjinj, fun g v => ?_⟩
    exact hjeq (incl g) v
  have hW : IsCrys ((D.loc (D.nd.l i)).PD K') W.ρ :=
    (subsum_crys (PD := (D.loc (D.nd.l i)).PD K') (Ms := Ms') (hc := hc')
      (hF := hFont (D.nd.l i) K' (D.nbr i w hw).LL) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W) (hA := hsub)).1
  have hcyc : ∀ g : ↥(GK K'),
      ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
        ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) (incl g) : (Br.LL D.nbr i w hw)ˣ) :
          Br.LL D.nbr i w hw) := by
    intro g
    have e1 := (D.loc (D.nd.l i)).PD_χ K' g
    have e2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (incl g)
    change algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((((D.loc (D.nd.l i)).PD K').χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (incl g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i])
    rw [e1, e2]
    rfl
  have hD' : IsDual1 ((D.loc (D.nd.l i)).PD K') W.ρ W'.ρ PX := by
    refine ⟨fun g v y => ?_, h2, h3, h4⟩
    rw [hcyc]
    exact h1 (incl g) v y
  have hW' : IsCrys ((D.loc (D.nd.l i)).PD K') W'.ρ :=
    (hFont (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1 W W' PX hD' hW
  exact hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h X' hW'

end GlobalTheory.SummandDualDR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorLocalFieldIsCrystallineOverFamilyField
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocCrysU

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g), ∃ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hFo i r hr Xs w hw n hP k M hSub hM
  obtain ⟨K', h, hN, hFi, hS, Sig, Fr, -, -, -, -, hx⟩ := hP
  obtain ⟨-, x₀, hx₀, j, hjinj, hjeq⟩ := hSub
  refine ⟨K', h, ?_⟩
  haveI := GlobalTheory.Pass.LocDirect.isTopRing i w hw
  have hcont := (GlobalTheory.Pass.FamCont.stepCont D i r hr x₀).1
  have hc1 : Continuous (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) :=
    GlobalTheory.PotDual.continuous_loc D i w hw _ hcont
  have hinc : Continuous (Subgroup.inclusion (GK_le h)) :=
    Continuous.subtype_mk continuous_subtype_val _

  have hpc := (hx ⟨x₀, hx₀⟩).1
  have hcr := ((GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hFi hS
    _ (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)))).2).1 hpc
  let A₁ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw (rTwO D.nd i r x₀)) hc1)
  let A₀ := GlobalTheory.Pass.FinDesc.resG (Subgroup.inclusion (GK_le h)) hinc (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM)

  let f := Br.toLLK (D.nbr i w hw)
  let J := (LinearMap.toMatrix' j).map f
  obtain ⟨jl, hjl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.2 hjinj)
  have hJl : ((LinearMap.toMatrix' jl).map f) * J = 1 := by
    rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hjl, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero f) (map_one f)]
  let ι : A₀.V →ₗ[Br.LL D.nbr i w hw] A₁.V := Matrix.toLin' J
  have hinj : Function.Injective ι := by
    have e : ∀ z : Fin k → Br.LL D.nbr i w hw, ((LinearMap.toMatrix' jl).map f).mulVec (J.mulVec z) = z := fun z => by
      rw [Matrix.mulVec_mulVec, hJl, Matrix.one_mulVec]
    intro u v huv
    have huv' : J.mulVec u = J.mulVec v := huv
    rw [← e u, ← e v, huv']
  have hJeq : ∀ γ : GE D.nd, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply, Matrix.toLin'_apply, hjeq]
  have h1 : ∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x) := by
    intro g (x : Fin k → Br.LL D.nbr i w hw)
    have hmat : J * Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g) =
        Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g) * J := by
      rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJeq]
    have key : J.mulVec ((Br.loc D.nbr i w hw M (Subgroup.inclusion (GK_le h) g)).mulVec x) =
        (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) (Subgroup.inclusion (GK_le h) g)).mulVec (J.mulVec x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
    exact key
  have hU : ∀ g, ∀ u ∈ LinearMap.range ι, A₁.ρ g u ∈ LinearMap.range ι := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A₀.ρ g x, h1 g x⟩
  let A₂ := A₁.quot (LinearMap.range ι) hU
  have hF := hFo (D.nd.l i) K' (D.nbr i w hw).LL
  exact ((hF.1 A₀ A₁ A₂ ι (LinearMap.range ι).mkQ h1 (fun _ _ => rfl) hinj (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm).1 hcr).1

end GlobalTheory.Pass.LocCrysU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStable
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotTwist

theorem frob : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
    finrank ℚ_[l] ↥K.1 = 1 → ∃ F : ↥(GK K), (pc P h hN hF hS).IsFrob F := by
  intro l _ P K K' h hN hF hS hK
  have hbot : K.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 hK
  obtain ⟨g, hg⟩ : ∃ g : GQ l, ∀ x : ↥(Loc.K0 K'), g x = (((P.PD K').σ x : ↥(Loc.K0 K')) : Om l) := by
    let τ : ↥(Loc.K0 K') →ₐ[ℚ_[l]] Om l := (Loc.K0 K').val.comp (P.PD K').σ
    exact ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
      fun x => τ.liftNormal_commutes (Om l) x⟩
  have hmem : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hbot] at hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes a
  refine ⟨⟨g, hmem⟩, fun c => ?_⟩
  change (P.PD K).actB _ _ = algebraMap _ _ ((P.PD K').σ c)
  rw [P.PD_actB]
  exact P.actQ_Kur g (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) c)
    (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) ((P.PD K').σ c)) (hg c)

theorem main : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  intro D hT i w hw hdeg r Xs K' h hN hF hS Sig0 c n hc hcard hcont hx hχ1 hχ2

  have hequiv : ∀ (g : Br.G D.nbr i w hw) (v : Br.LL D.nbr i w hw),
      (LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm
        (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1)) g v) =
      (D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w)) g
        ((LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm v) := by
    intro g v
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [WeaklyAdmissibleFiltrations.charRep, LocBridge.rep, Br.locChi, Br.chiG, chiGL, Br.ι, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, mul_comm]
  obtain ⟨tr1, tr2⟩ := GlobalTheory.HTW.Rec.potCrysData_transport (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ _ hequiv
  have htw : ∀ x : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := fun x =>
    GlobalTheory.TwistPotCrys.twist_potCrys D hT i w hw r x K' h hN hF hS Sig0 c (hcont x x.2) (hx x x.2).1 (hx x x.2).2 (tr1 hχ1) (tr2 _ hχ2)
  obtain ⟨Fr, hFr⟩ := frob (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' h hN hF hS hdeg
  have h1 : (1 : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) ∈ Sig0.image (fun a => a * c⁻¹) :=
    Finset.mem_image.2 ⟨c, hc, mul_inv_cancel c⟩
  obtain ⟨Sig, hsub, h1', hst, hit⟩ := GlobalTheory.frobStable_inertial_subset (pc (D.loc (D.nd.l i)) h hN hF hS)
    (fun x : ↥Xs => matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) (Fr : Br.G D.nbr i w hw) _ h1 (fun x => (htw x).2)
  exact ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1',
    le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hcard), fun x => ⟨(htw x).1, hit x⟩⟩

end GlobalTheory.PotTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoEALe
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.UnramifiedChar

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

variable {l : ℕ} [Fact l.Prime]

theorem val_mem_OL (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) (g : ↥(GK K)) :
    ((μ g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  let d : ↥(GK K) →* Om l :=
    ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →* Om l).comp ((Units.coeHom ↥LL.1).comp μ)
  have hd : Continuous d := continuous_subtype_val.comp hμ
  exact (GlobalTheory.Per.Val.mem_OL_iff LL _).2 (norm_eq_one_of_compact d hd g).le

def unitLat (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := ↥LL.1
  ρ := charRep μ
  cont := fun x => hμ.mul continuous_const
  L := GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.charLat Subtype.val_injective μ fun g => ⟨⟨_, val_mem_OL K LL μ hμ g⟩, rfl⟩

theorem isCrys_and_multV_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  intro l _ P AI T K LL μ hμ hI
  obtain ⟨hc, hj⟩ := GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI T K LL (unitLat K LL μ hμ)
    (fun g hg (x : ↥LL.1) => by
      change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x = x
      rw [hI g hg, Units.val_one, one_mul])
  change IsCrys (P.PD K) (charRep μ) at hc
  change ∀ τ a, IsJumpV (P.PD K) (charRep μ) τ a → a = 0 at hj
  refine ⟨hc, fun τ b => ?_⟩
  obtain ⟨hcomp, -⟩ := GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)
  obtain ⟨hfd, -, hdr⟩ := hcomp τ
  haveI := hfd
  set_option synthInstance.maxHeartbeats 200000 in
  have hdim : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdr (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL ↥LL.1 (charRep μ) hc).1, finrank_self]
  have hnj : ∀ a, a ≠ 0 → multV (P.PD K) (charRep μ) τ a = 0 := fun a ha =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump (P.PD K) (charRep μ) τ a (fun h => ha (hj τ a h))
  split_ifs with hb
  · subst hb
    obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (charRep μ) τ
    obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (charRep μ) τ
    have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) (charRep μ) τ (min lo 0) (max hi 1) (by omega)
    rw [hlo _ (min_le_left _ _), hhi _ (le_max_left _ _), finrank_bot, Nat.cast_zero, sub_zero, hdim,
      Finset.sum_eq_single (0 : ℤ) (fun a _ ha => hnj a ha)
        (fun h => absurd (Finset.mem_Ico.2 ⟨min_le_right _ _, by omega⟩) h)] at hsum
    exact_mod_cast hsum
  · exact hnj b hb

end GlobalTheory.UnramifiedChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacter
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Generic

variable {g : ℕ} [Fact g.Prime]

theorem br_zero_self {d : ℕ} (M : Mt g d) : br 0 d M = M := by
  funext i j
  simp [br, entN, i.isLt, j.isLt]

theorem res_zero_self {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g d) : res 0 d χ 1 h = χ h := by
  unfold res
  have hI : ∀ x : Gn g d, InPar 0 (x : Mt g d) := fun x i j hj _ => absurd hj (Nat.not_lt_zero _)
  have hT : ∀ x : Gn g d, tl 0 (x : Mt g d) = ((1 : Gn g 0) : Mt g 0) := fun x => by
    funext i; exact i.elim0
  simp only [hI, hT, br_zero_self, true_and, zero_mul, pow_zero, inv_one, one_mul, Units.val_inj]
  rw [Finset.sum_ite_eq']
  simp

theorem wh_zero_fun (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : wh ψ (fun _ : Gn g n => (0 : ℂ)) = 0 := by
  simp [wh, tr]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

end GlobalTheory.GLq.Generic

theorem GlobalTheory.GLq.wh_cusp_pos : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  intro g _ ψ hψ d χ hc
  have hc' := hc
  obtain ⟨hd, hirr, _⟩ := hc'
  have hder := _root_.GlobalTheory.GLq.DegDer.one_eq_sum_der g ψ hψ d χ hd (GlobalTheory.GLq.Generic.isClass_of_isIrr hirr)
  rw [Finset.sum_eq_single 0] at hder
  rotate_left
  · intro m hm hm0
    have hmd : m < d := Finset.mem_range.mp hm
    have hz : res m (d - m) χ 1 = fun _ => 0 := by
      funext y
      exact _root_.GlobalTheory.GLq.res_cusp_eq_zero g d m χ hc (Nat.pos_of_ne_zero hm0) hmd 1 y
    have : der ψ m χ 1 = 0 := by
      show wh ψ (res m (d - m) χ 1) = 0
      rw [hz]
      exact GlobalTheory.GLq.Generic.wh_zero_fun ψ _
    rw [this, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr hd) h0
  have h0 : der ψ 0 χ 1 = wh ψ χ := by
    change wh ψ (n := d) (res 0 d χ 1) = wh ψ χ
    congr 1
    funext h
    exact GlobalTheory.GLq.Generic.res_zero_self χ h
  rw [h0] at hder
  obtain ⟨V, _, hV⟩ := hirr
  have hchar : IsChar χ := ⟨V, hV⟩
  obtain ⟨d', hd'pos, hd'⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g d) (eU g d ψ) χ).2.1 ⟨V, ‹_›, hV⟩
  obtain ⟨n, hn⟩ := (_root_.GlobalTheory.GLq.trIdem (Gn g d) (eU g d ψ) χ).1 (_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g d 0 0 ψ).1 hchar
  have hwh : wh ψ χ = n := hn
  refine ⟨n, Nat.pos_of_ne_zero ?_, hwh⟩
  rintro rfl
  rw [hwh, Nat.cast_zero, zero_mul, hd'] at hder
  exact absurd hder (by exact_mod_cast hd'pos.ne')
end
end

