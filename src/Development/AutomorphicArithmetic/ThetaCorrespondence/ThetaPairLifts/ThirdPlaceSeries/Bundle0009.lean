module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartEq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem eq_one_twist_t_of_mulVec_eigen (_h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hg : HG D.nd D.naut i)
    (p : Part D.naut.CG) (Rk : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)))
    (hR : UpperTheory.GalS.IsStringRepN D i p Rk) (ha : p.a = 1) (hd : p.d = D.R.t) (u : Fin p.a → Qbar (D.nd.l i)) (hu0 : u ≠ 0)
    (hu : ∀ g, ((Rk g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i))).mulVec u =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) • u) :
    p = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
  have h3 := _root_.GlobalTheory.HeckeCharacterEquality.hecke_character_equality_of_realisation
  rcases p with ⟨a, π, d⟩
  dsimp only at ha hd
  subst ha hd
  have hu00 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
  have h00 : ∀ g, ((Rk g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) := fun g => by
    have := congrFun (hu g) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hu00 this
  have hπ := h3 D hA i π (D.naut.tw (D.naut.muC i) D.naut.etaTinv) _ Rk hR.2.2 (h4 D hA i hg Rk h00)
  subst hπ
  rfl
end GlobalTheory.EigenPoint
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCount
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.ResidualRankCount
section Alg
variable {Γ : Type} [Group Γ]
end Alg
section Lists
end Lists
section Psi
end Psi
theorem residual_count_alt_alt : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  intro hV hS hU D hA hRb i hg r hr x Pa R hR hcp
  classical
  obtain ⟨B, _, _, _, j, hj, hran, hmax, hmod⟩ := hV (D.nd.l i)
  obtain ⟨ψ, hψ, φ, hφ⟩ := exists_psi D.nd D.naut i j hj hran hmax
  choose ρ0 P hP using fun k : Fin Pa.length => hmod (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (R k) (_root_.UpperTheory.GalS.strN' (hR k)).1
  choose L hL1 hL2 using fun k : Fin Pa.length =>
    hS (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (mapRep (IsLocalRing.residue B) (ρ0 k))
  obtain ⟨rb, hrb⟩ := hRb i hg
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.1.1.2.2.2.2.2.2.2.2.1
  have hirr := (hA.2.1 i hg rb hrb).1
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  let cR : ℕ → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (IsLocalRing.ResidueField B)) := fun c =>
    (Units.map (algebraMap (IsLocalRing.ResidueField B)
      (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))).toMonoidHom).comp
      ((Units.map (φ.comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i c))
  let τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (IsLocalRing.ResidueField B)ˣ :=
    (Units.map ((IsLocalRing.residue B).comp ψ).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)⁻¹
  let L1 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    ⟨D.R.r, mapRep φ rb⟩ :: (Finset.Icc 1 D.R.t).toList.map fun c => ⟨1, cR c⟩
  let L2 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    (List.finRange Pa.length).flatMap fun k => (List.range (Pa.get k).d).flatMap fun a =>
      (L k).map fun p => ⟨p.1, Formalism.MainNotions.SumRepresentations.At.twGL p.2 (τ ^ a)⟩
  have h1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hr1, _root_.GlobalTheory.StringRepresentationDecomposition.irr_transfer_absIrr hr1 rb (D.naut.kFbar i) hirr φ⟩
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨le_rfl, absIrr_id le_rfl _ fun W _ => sub_fin_one W⟩
  have h2 : ∀ p ∈ L2, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    obtain ⟨k, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨a, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hq1, hq2⟩ := hL1 k q hq
    exact ⟨hq1, absIrr_id hq1 _ fun W hW => hq2.2.2 W le_top (isInv_of_twGL _ _ W hW)⟩
  have hjψ : j.comp ψ = iotaOQ D.nd D.naut i := RingHom.ext hψ
  have hs : ∀ g, j (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) = (epsQ D i g)⁻¹ := by
    intro g
    rw [hψ, map_units_inv]
    rfl
  have hBid : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map ψ =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((ρ0 k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) B).charpoly).scaleRoots
          (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) ^ a) := by
    intro g
    apply Polynomial.map_injective j hj
    rw [Polynomial.map_map, hjψ, ← Matrix.charpoly_map]
    show ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly = _
    rw [hcp g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow, hs, hP k g, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  have hkA : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    rw [← Polynomial.map_map, hBid g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow]
    all_goals rfl
  have hcpL1 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) := by
    intro g
    have hφ' : φ.comp (IsLocalRing.residue (D.nd.O i)) = (IsLocalRing.residue B).comp ψ := RingHom.ext hφ
    have hf : (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
        (IsLocalRing.residue (D.nd.O i))).charpoly = _ :=
      (Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x g).symm
    rw [← hφ', ← Polynomial.map_map, ← Matrix.charpoly_map, hf, Polynomial.map_mul, Polynomial.map_prod]
    simp only [L1, List.map_cons, List.prod_cons, List.map_map]
    congr 1
    · exact Matrix.charpoly_map _ φ
    · rw [Finset.prod_map_toList]
      refine Finset.prod_congr rfl fun c _ => ?_
      show (algebraMap (IsLocalRing.ResidueField B) (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))
        (φ (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)))).charpoly = _
      rw [charpoly_scal, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hcpL2 : ∀ g, (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    simp only [L2]
    rw [prod_map_flatMap, Fin.prod_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [prod_map_flatMap, prod_range_list]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [hL2 k g, scaleRoots_list_prod]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    show ((Formalism.MainNotions.SumRepresentations.At.twGL q.2 (τ ^ a) g : GL _ _) :
      Matrix (Fin q.1) (Fin q.1) (IsLocalRing.ResidueField B)).charpoly = _
    rw [charpoly_twGL, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have h3 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod := fun g => by
    rw [hcpL1 g, hcpL2 g, hkA g]
  have hrk := hU (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) L1 L2 h1 h2 h3
  refine ⟨fun k => (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ), fun k => ⟨?_, ?_⟩, ?_⟩
  · show (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ).sum = _
    rw [Multiset.sum_coe, ← (charpoly_list_monic (L k) 1).2, ← hL2 k 1, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  · intro a ha
    rw [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact (hL1 k p hp).1
  · have e1 : ((L1.map fun p => p.1 : List ℕ) : Multiset ℕ) = D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
      have : (L1.map fun p => p.1) = D.R.r :: List.replicate D.R.t 1 := by
        simp only [L1, List.map_cons, List.map_map, List.cons.injEq, true_and]
        refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        rfl
      rw [this, ← Multiset.cons_coe, Multiset.coe_replicate]
    have e2 : ((L2.map fun p => p.1 : List ℕ) : Multiset ℕ) =
        ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) := by
      simp only [L2, List.map_flatMap, List.map_map, Function.comp_def, coe_flatMap, sum_range_const]
      rw [Fin.sum_univ_def]
    show ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) = _
    rw [← e2, ← hrk, e1]
end GlobalTheory.ResidualRankCount
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem residual_irreducible_of_theorem_three_prime_alt (D : D7) (h : _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D) (hAN : SumRepresentations.adm5 D) (hBN : LitBNIrr (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))
    (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) : ResidualIrreducibleRankR D :=
  residual_irreducible_of_theorem D (_root_.Formalism.MainNotions.AdmissibleThreePrime.theorem_three_prime_holds_alt_alt D h) hAN hBN hrho hdz
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfLive
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem setting_of_live_alt_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
      GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  intro hC D h32 hS i hZ hL
  classical
  obtain ⟨rep, hr⟩ := (h32 i).1.2
  have hG1 := ((h32 i).2.2 rep hr).1
  have hG3 := _root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1
  have hJ := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i rep hr (hG3.1 (Or.inr hL)) (hS i)
  let ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) := fun x =>
    if hx : x ∈ D.nd.Z i then Classical.choose (hZ x hx (rep x) (hr x)) else 1
  have hρ : ∀ x ∈ D.nd.Z i, ∃ e, IsDecomp (t := D.R.t) (rep x) (ρ x) (D.nd.chi i) e := by
    intro x hx
    have := Classical.choose_spec (hZ x hx (rep x) (hr x))
    simp only [ρ, dif_pos hx]
    exact this
  obtain ⟨π, hπ, r0, ρ0, hr0, h0, habs⟩ := hL
  refine ⟨rep, ρ, hr, D.nd.T_local i, D.nd.T_sep i, fun x => ?_, fun h d => ?_,
    hJ, hG3.2, hρ, fun x hx => ?_⟩
  · have hss := (hr x).2.1
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W fun g v hv => hW g v hv
    exact ⟨W', fun g v hv => h1 g v hv, h2⟩
  · obtain ⟨f, hf⟩ := hG1 h d
    have : (fun x => (mat (rep x) h).charpolyRev.coeff d) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [this]
    exact f.2
  · have hpos := pos_of_absIrrSub _ habs
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
    refine absIrrSub_of_span_eq_top hpos _ ?_
    refine span_eq_top_of_trace_eq _ (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0) (fun g => ?_)
      (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
    rw [mat_mapRep, mat_mapRep, Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
      _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.residual_charpoly_eq_alt_alt hC D h32 i rep hr x π (ρ x) ρ0 (hρ x hx) r0 hr0 h0 g]
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthCharacterEqualityHoldsAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_character_equality_holds_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw
    have e := congrArg (fun a => D.naut.lpTw a (-s)) ((h w hw).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthDecomposition
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_string_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt := by
  first | exact @_root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | exact _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt | (intros; apply _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightPurity
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end GlobalTheory.FrobeniusCharacterNorms
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_weight_purity_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  intro D hA i x P Pa hxP hBC k R hR j hj hv
  have hAut : At.TieAut D.nd D.naut := hA.1.1.1.2.1
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hp : Pa.get k ∈ Pa := List.get_mem Pa k
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪
      {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)).Finite := by
    have h1 : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
      ((placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
        (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
    exact (h1.union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (Pa.get k).π))).union
      (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (D.naut.muC i)))
  have hne := (hC _ hfin).symm ▸ Set.mem_univ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
  obtain ⟨σ, ⟨w, hw, hsp, B, hB, hσ⟩⟩ : Set.Nonempty {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪
      ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hne
    exact hne
  simp only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_setOf_eq, not_not] at hw
  have hl := hw.1.1.1.1
  have hwo : SplitOut D.nd i w := ⟨hsp, hl, hw.1.1.1.2, hw.1.1.2⟩
  have huπ := hw.1.2
  have huμ := hw.2
  have hR := _root_.UpperTheory.GalS.strN' hR
  have hwd := (hR.2.2 w hl).eq_of_unr ((D.naut.unr_tw _ _).2 huπ)
  have hU : D.naut.unr (D.naut.wdOf i R w) := by rw [hwd]; exact (D.naut.unr_tw _ _).2 huπ
  have hF := D.naut.wdOf_frob i R w hl hR.1 hU B σ hB hσ
  rw [hwd, D.naut.frobEig_tw _ _ huπ] at hF
  obtain ⟨v, hv0, hvg⟩ := hv
  have h1 := hvg σ
  set M : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i)) :=
    ((R σ : GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))) with hM
  set c : Qbar (D.nd.l i) := iotaOQ D.nd D.naut i (chi1 D.nd i σ) with hc
  have he0 : epsQ D i σ ≠ 0 :=
    ((Units.isUnit (Formalism.MainNotions.N.Glob.epsO D.nd i σ)).map (iotaOQ D.nd D.naut i)).ne_zero
  have hMv : M.mulVec v = (epsQ D i σ ^ j * c) • v := by
    have h2 := congrArg (fun u => (epsQ D i σ ^ j) • u) h1
    simp only [smul_smul, inv_pow] at h2
    rw [mul_inv_cancel₀ (pow_ne_zero _ he0), one_smul] at h2
    exact h2
  have hdet : (Matrix.scalar (Fin (Pa.get k).a) (epsQ D i σ ^ j * c) - M).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hMv]
    ext t
    simp [Matrix.scalar_apply]
  have hroot : (M.charpoly.map (D.naut.iotaQC i).toRingHom).IsRoot
      ((D.naut.iotaQC i).toRingHom (epsQ D i σ ^ j * c)) :=
    Polynomial.IsRoot.map (D.naut.iotaQC i).toRingHom
      (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hdet)
  rw [hF] at hroot
  have hmem := (Polynomial.mem_roots (Polynomial.monic_multiset_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero).2 hroot
  rw [Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨α, hα, hαe⟩ := Multiset.mem_map.1 hmem
  have hα1 := (_root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hA.1.1.1 hA.1.2 i P Pa hBC (Pa.get k) hp w huπ α hα).1
  have hq0 : 0 < normV w := normV_pos w
  have hq1 : (1 : ℝ) < normV w := GlobalTheory.LocalInv.one_lt_normV w
  have hε : D.naut.iotaQC i (epsQ D i σ) = (normV w : ℂ) := eps_frob i hl hB hσ
  have hχ := norm_first_character_frobenius hAut i hwo huμ hB hσ
  have hn := congrArg norm hαe
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, hε, norm_mul, norm_pow,
    Complex.norm_natCast_cpow_of_pos hq0, Complex.ofReal_re, Complex.norm_natCast] at hn
  rw [hc, hχ, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)] at hn
  have hx := hα1.exp_eq (UpperTheory.GalN.one_lt_q w) hn (2 * (j : ℤ) + D.R.t - (Pa.get k).d) (by push_cast; ring)
  have hz : (((Pa.get k).d : ℤ) - 1 - 2 * j : ℝ) = ((D.R.t : ℤ) - 1 : ℝ) := by push_cast; linarith
  exact_mod_cast hz
end GlobalTheory.FrobeniusCharacterNorms
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameAnyAtPlace
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_any_at_pl_gw : ∀ D : D7, _root_.UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → _root_.UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  first | exact @_root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt | exact _root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt | (intros; apply _root_.GlobalTheory.TypeLeaf.tameAnyAt_fixed_alt_alt <;> assumption)
end
end

