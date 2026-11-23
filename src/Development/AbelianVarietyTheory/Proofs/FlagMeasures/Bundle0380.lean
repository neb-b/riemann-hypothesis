module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IoEqOfGraph
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SelfDualPoint

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.CS

theorem mem_genus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate) {L L' : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L') (hd : dual h L = L) (hd' : dual h L' = L') :
    L' ∈ genus h L := by
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩
  have key : ∀ M : Submodule (𝓞 K) V, M.FG → dual h M = M → ∀ P : Ideal (𝓞 K), P.IsPrime →
      IsUnimodularAt h P M := fun M hM hdM P hP => by
    have a := (locDual (𝓞 K) K V h hs hstar M hM).1 P hP
    have b := a.2.trans a.1.symm
    rwa [hdM] at b
  have full : ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → dual h M = M →
      Submodule.IsFullLattice K M := by
    intro M hM hdM
    classical
    let b := Module.finBasis K V
    let B : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
    let N := M ⊔ B
    have hNfg : N.FG := hM.fg.sup (Submodule.fg_span (Set.finite_range b))
    have hNspan : Submodule.span K (N : Set V) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← b.span_eq]
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (show B ≤ N from le_sup_right) (Submodule.subset_span ⟨i, rfl⟩)
    have hN : Submodule.IsFullLattice K N :=
      { toIsLattice := Submodule.IsLattice.of_fg K hNfg, span_eq_top := hNspan }
    have hNd := (dualLattice (𝓞 K) K V h hs hn hstar N hN).1
    have hle : dual h N ≤ M := by
      rw [← hdM]
      exact (dualBasic (𝓞 K) K V h hs hstar).1 M N le_sup_left
    letI : Submodule.IsFullLattice K (dual h N) := hNd
    letI : Submodule.IsLattice K M := hM
    exact Submodule.IsFullLattice.of_le K hle
  have hLf := full L hL hd
  have hL'f := full L' hL' hd'
  exact ⟨hL'f, fun P hP => GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn L L' hLf hL'f P hP
    (key L hL.fg hd P hP.isPrime) (key L' hL'.fg hd' P hP.isPrime)⟩

theorem lamX_eq_globLat (I : AutInst) (xf : I.Gf) : lamX I (1, xf) = globLat xf.1 I.L := by
  have e : I.Lf = latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf latS
    congr 1
    ext u
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.2, hx⟩, fun ⟨x, hx, hx'⟩ => ⟨⟨x, hx⟩, hx'⟩⟩
  unfold lamX
  rw [e]
  exact Submodule.span_eq (globLat xf.1 I.L)

theorem exists_lamX_eq : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  intro I Λ hΛ hd
  have hs : ∀ e, (I.cm.sig : I.E →+* I.E) ((I.cm.sig : I.E →+* I.E) e) = e := fun e => star_star e
  have hfix : ∀ e : I.E, I.cm.sig e = e → ∃ a : I.F, algebraMap I.F I.E a = e := fun e he => (I.cm.fixed e).1 he
  let h : (Fin I.n → I.E) →ₗ⋆[I.E] (Fin I.n → I.E) →ₗ[I.E] I.E := formJ (I.cm.sig : I.E →+* I.E) hs I.J 1
  obtain ⟨hsym, hap⟩ := Formalism.UG.P.hermitian_form_symmetry_holds I.E _ hs (Fin I.n) I.J 1 (map_one _) I.J_herm
  replace hsym : h.IsSymm := hsym
  replace hap : ∀ x y, h x y = hform (starRingEnd I.E) I.J x y := fun x y => (hap x y).trans (one_mul _)
  have hr : ∀ y, (∀ x, h x y = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_mulVec_eq_zero I.J_det (funext fun i => ?_)
    have := hy (Pi.single i 1)
    rw [hap, hform, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hn : h.Nondegenerate := ⟨fun x hx => hr x fun y => by rw [← hsym.eq, hx, map_zero], hr⟩
  have hdual : ∀ M : Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ x, x ∈ M ↔ ∀ y ∈ M, hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) →
      dual h M = M := fun M hM => by
    ext x
    rw [dualBasic_mem_dual, hM x]
    simp only [hap, Submodule.mem_one, RingHom.mem_range]
  obtain ⟨g, hg, e⟩ := GlobalTheory.Mass.Genus.exists_globLat_eq (J := I.J) hs hfix (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span Λ (mem_genus h I.cm.cmUnram hsym hn (Submodule.IsLattice.of_fg I.E I.L_fg) hΛ (hdual _ I.L_dual) (hdual _ hd))
  exact ⟨⟨g, hg⟩, (lamX_eq_globLat I _).trans e⟩

end GlobalTheory.SelfDualPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlaceStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_of_unimodular_lattices_at_place : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L L' : Submodule (𝓞 K) V), Submodule.IsFullLattice K L → Submodule.IsFullLattice K L' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P L → IsUnimodularAt h P L' → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  first | exact @GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt | exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt | (intros; apply GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar
section
noncomputable section

open NumberField GlobalTheory.DegCnt

namespace GlobalTheory.OrthoLattice

theorem isCMField_of_star (K : Type) [Field K] [NumberField K] [StarRing K] (htc : IsTotallyComplex K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField K := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hmem : ∀ x : K, star x = x → x ∈ maximalRealSubfield K := fun x hx ψ => by
    have := hst ψ x
    rw [hx] at this
    exact this.symm
  have hfix : ∀ x : maximalRealSubfield K, star (x : K) = x := fun x =>
    φ.injective (by rw [hst]; exact x.2 φ)
  obtain ⟨a, ha⟩ : ∃ a : K, star a ≠ a := by
    by_contra h
    push Not at h
    apply IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hst, h]
  set d : K := a - star a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 ha.symm
  have hds : star d = -d := by simp [hd]
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : (s : K) + (t : K) * d = 0 := by simpa [Subfield.smul_def] using h
    have h2 := congrArg star h1
    rw [star_add, star_mul, hfix, hfix, hds, star_zero] at h2
    have h3 : (s : K) = 0 := by linear_combination (h1 + h2) / 2
    have h4 : (t : K) * d = 0 := by linear_combination h1 - h3
    exact ⟨Subtype.ext h3, Subtype.ext ((mul_eq_zero.1 h4).resolve_right hd0)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro x _
    have h1 : star ((x + star x) / 2) = (x + star x) / 2 := by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm]
    have h2 : star ((x - star x) / (2 * d)) = (x - star x) / (2 * d) := by
      rw [star_div₀, star_sub, star_star, star_mul, star_ofNat, hds]
      field_simp
      ring
    have h3 : x = (⟨_, hmem _ h1⟩ : maximalRealSubfield K) • (1 : K) +
        (⟨_, hmem _ h2⟩ : maximalRealSubfield K) • d := by
      simp only [Subfield.smul_def, smul_eq_mul]
      field_simp
      ring
    rw [h3]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact ⟨⟩

theorem hasOrtho : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K := by
  intro K _ _ st hc
  have := isCMField_of_star K hc.1 hc.2.1
  have hs : st = IsCMField.starRing K := by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h : ∀ x, st.star x = IsCMField.complexConj K x := fun x =>
      φ.injective (by rw [IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ x)
    obtain @⟨@⟨@⟨@⟨f⟩, _⟩, _⟩, _⟩ := st
    obtain rfl : f = IsCMField.complexConj K := funext h
    rfl
  subst hs
  let := IsCMField.starRing K
  intro W _ _ _ _ _ k hk hp ⟨L, hL, hU⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hnd : k.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · by_contra h0
      have := hp φ x h0
      rw [hx x] at this
      simp at this
  let S : Formalism.BasicNotions.HSpace K := Formalism.BasicNotions.HSpace.mk W k hk hnd (Module.finrank K W) rfl (Module.finBasis K W)
    (fun _ => (Module.finrank K W, 0)) L hL hU
  have hsig : S.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef
    ((GlobalTheory.Proof.GenusMassSignature.pos_iff_posDef hc.1 hc.2.1 S τ).1 (hp τ))
  obtain ⟨b, hb, ho⟩ := GlobalTheory.DefiniteOrthonormal.exists_orthonormal hc S hsig fun _ => rfl
  exact ⟨_, b, hb, hb.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _), rfl, ho⟩

end GlobalTheory.OrthoLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIdentificationEqOfGlobalLatticesEq
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.IotaLocal

theorem iotaGraph_eq_of_gdat : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ :=
  GlobalTheory.IotaLocA.io_eq_of_graph

end GlobalTheory.Unfold.IotaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatEqOfIndep
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm

section Gen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

theorem sum_smul_sum (e : Fin m → V) (P Q : Matrix (Fin m) (Fin m) K) (b : Fin m) :
    ∑ a, P a b • ∑ c, Q c a • e c = ∑ c, (Q * P) c b • e c := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem fm_conj {e f : Fin m → V} (ψ τ : V ≃ₗ[K] V) {P B : Matrix (Fin m) (Fin m) K} (hP : IsUnit P.det)
    (hψ : ∀ b, ψ (e b) = ∑ a, P a b • f a) (hτ : FM f τ B) :
    FM e (fun y => ψ.symm (τ (ψ y))) (P⁻¹ * B * P) := by
  intro b
  have hτ' : ∀ a, τ (f a) = ∑ c, B c a • f c := hτ
  apply ψ.injective
  show ψ (ψ.symm (τ (ψ (e b)))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearEquiv.apply_symm_apply, hψ b, map_sum]
  simp only [map_smul, hτ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sum_smul_sum, map_sum]
  simp only [map_smul, hψ]
  rw [sum_smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_assoc P⁻¹ B P, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

theorem mat_eq_of_indep {e : Fin m → V} (he : LinearIndependent K e) (y : Fin m → V)
    {M M' : Matrix (Fin m) (Fin m) K} (h1 : ∀ b, y b = ∑ a, M a b • e a) (h2 : ∀ b, y b = ∑ a, M' a b • e a) :
    M = M' := by
  ext c b
  have h0 : ∑ i, (M i b - M' i b) • e i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h1 b, ← h2 b, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 he) _ h0 c)

end Gen

end GlobalTheory.HL.CovDict

namespace GlobalTheory.HL.CovDict

open Formalism.L2.SG.Pf.VolPinAsm Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

theorem dict_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ (γw s s' : X.B.I.Ginf), Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t₀.pt.1 = s * γw * s'⁻¹ → ∃ σ : Formalism.L2.SG.RealObj.FreeE w → ℂ, (∀ p, ‖σ p‖ = (D.host.rdE : ℝ) ^ (p.1.2.val - p.1.1.val)) ∧ ∃ A : InfinitePlace X.B.I.F → (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ v x x' p, (∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) → A v x p - x p = A v x' p - x' p) ∧ ∀ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n → c.grp ρ n ∈ G.K0 → ∀ v, Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * x.1 * s) v = A v (fun p => σ p * Formalism.L2.SG.Pf.VolPinAsm.phiV X v (GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) p.1.1 p.1.2)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c t₀ ρ U U' hMv _ γw s s' _ _ hs' hpt
  obtain ⟨-, -, hU', -, hρ'⟩ := hMv
  have hrd : (0 : ℝ) < D.host.rdE := (Formalism.BasicNotions.rdE_pos_le D).1
  have hrdc : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd.ne'
  have hU'u : IsUnit U'.det := by rw [up_det hU']; exact isUnit_one
  choose S hSU hS using fun v => inS_frame (hs' v)
  have hSu : ∀ v, IsUnit (S v).det := fun v => by rw [up_det (hSU v)]; exact isUnit_one
  set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v =>
    U'.map (phiV X v) * S v with hN
  have hNU : ∀ v, IsUpUni (N v) := fun v => up_mul (upUni_map (phiV X v) hU') (hSU v)
  have hNu : ∀ v, IsUnit (N v).det := fun v => by rw [up_det (hNU v)]; exact isUnit_one
  refine ⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1), fun p => ?_,
    fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx, ?_⟩
  · rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hrd.le]
  intro x n hxn hK v
  funext p

  have hStm : c.grp ρ n ∈ G.St := fun q => by
    obtain ⟨g', hg', he⟩ := hK q
    exact ⟨g', hg'.1.1, he⟩
  obtain ⟨B, hBU, hBf, hBblk⟩ :=
    (_root_.GlobalTheory.HL.StCoord.stab_coords D X Y u u' hSt hk w F00 F'0 FP hZ hGv hAt G c).1 _ hStm
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hli : LinearIndependent D.host.E G.f' := by
    have e : G.f' = fun a => c.e (frame F'0 a) := funext c.f'_eq
    rw [e]
    exact (Formalism.L2.SG.Pf.TupLift.frame_li F'0 hT').map' _ (LinearEquiv.ker _)
  have hB : GlobalTheory.HL.TraceConjugationCover.stMat G (c.grp ρ n) = B :=
    mat_eq_of_indep hli _ (GlobalTheory.HL.TraceConjugationCover.stMat_spec G _ ⟨B, hBf⟩) hBf
  rw [hB]

  set τ : (VS D).V ≃ₗ[D.host.E] (VS D).V := ρ.symm.trans (n.trans ρ) with hτdef
  have hτ : FM (frame F'0) τ B := by
    intro b
    apply c.e.injective
    have e1 : c.e (τ (frame F'0 b)) = c.grp ρ n (G.f' b) := by
      rw [c.f'_eq]; simp [GCoord.grp, τ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, hBf b, map_sum]
    simp only [map_smul, c.f'_eq]
  set ψ : (VS D).V ≃ₗ[D.host.E] (VS D).V := t₀.lin.trans ρ with hψdef
  have hψ : ∀ b, ψ ((X.Fu u').fvec b) = ∑ a, U' a b • frame F'0 a := by
    intro b
    show ρ (t₀.lin _) = _
    rw [← Formalism.L2.SG.Pf.FibreCounting.frame_apply]
    exact hρ' b
  have hFMm := fm_conj ψ τ hU'u hψ hτ
  have hFMm' : FM (X.Fu u').fvec (t₀.lin⁻¹ * n * t₀.lin) (U'⁻¹ * B * U') := by
    intro b
    rw [← hFMm b]
    show t₀.lin.symm (n (t₀.lin _)) = _
    simp [ψ, τ]
  have hγx : RatLink X t₀.pt t₀.lin := t₀.rep.2.1
  set zz := t₀.pt⁻¹ * x * t₀.pt with hzz
  have hzL : RatLink X zz (t₀.lin⁻¹ * n * t₀.lin) :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) hxn) hγx
  have hgrp : γw⁻¹ * (s⁻¹ * x.1 * s) * γw = s'⁻¹ * zz.1 * s' := by
    have e1 : zz.1 = t₀.pt.1⁻¹ * x.1 * t₀.pt.1 := by simp only [hzz, Prod.fst_mul, Prod.fst_inv]
    have e2 : γw = s⁻¹ * t₀.pt.1 * s' := by rw [hpt]; group
    rw [e1, e2]; group
  have hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
    intro a
    show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) =
      (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) := by
    have hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ :=
      (Matrix.inv_eq_right_inv (hmi (s' v))).symm
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _
    rw [hi]
  have hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det := by
    have := congrArg Matrix.det (hmi (s' v))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) *
      Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v) :=
    FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzL hFMm' v)) (hS v)
  have hG : (S v)⁻¹ * (U'⁻¹ * B * U').map (phiV X v) * S v = (N v)⁻¹ * B.map (phiV X v) * N v := by
    have hinv : (U'.map (phiV X v))⁻¹ = (U'⁻¹).map (phiV X v) :=
      Matrix.inv_eq_left_inv (map_inv_mul (phiV X v) hU'u)
    rw [show N v = U'.map (phiV X v) * S v from rfl, Matrix.mul_inv_rev, hinv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) *
      phiV X v (B q.1.1 q.1.2)) = B.map (phiV X v) - 1 := by
    ext c' d
    rw [Matrix.sub_apply, Matrix.map_apply]
    simp only [Yhat]
    split_ifs with hcd
    · rw [Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]
      field_simp
    · by_cases hlt : c' < d
      · rw [hBblk c' d (fun he => hcd ⟨hlt, he⟩), map_zero, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]
      · rcases lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq
        · rw [(hBU c' d).1 hgt, map_zero, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]
        · rw [heq, (hBU c' c').2 rfl, map_one, Matrix.one_apply_eq, sub_self]
  have hab : p.1.1 < p.1.2 := p.2.1
  have har : p.1.1.1 < D.R.rS := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)
  show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p
  unfold Formalism.L2.SG.RealObj.stCoord
  rw [hgrp, hu, Alin_apply, hY]
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2 := rfl
  rw [hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]
  have hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1 := Fin.ext rfl
  rw [hcs, conj_off (hNu v) (ne_of_lt hab)]
  have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) := by
    rw [← pow_add]; congr 1
    have : (p.1.2 : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.1 p.1.2.2
    have : (p.1.1 : ℕ) < p.1.2 := hab
    omega
  rw [hpow]
  field_simp

end GlobalTheory.HL.CovDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusOfIsUnimodular
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.ExGenus

open Formalism.HermitianLatticesTheory

private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  letI := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span K (L : Set V)
  change W = ⊤
  by_contra hw
  let b := Module.finBasis K V
  let e : V ≃ₗ⋆[K] V := (b.equivFun.trans (starLinearEquiv K)).trans b.equivFun.symm
  let g : V →ₗ[K] Module.Dual K W :=
    (LinearMap.domRestrict' W).comp (h.comp e.toLinearMap)
  have hd : Module.finrank K (Module.Dual K W) < Module.finrank K V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt hw
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hd)
  have hm (a : K) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    have hz : h (e x) y = 0 :=
      congrArg (fun f : Module.Dual K W => f ⟨y, Submodule.subset_span hy⟩)
        (LinearMap.mem_ker.mp hx)
    have hz' : h y (e x) = 0 := by
      exact hs.eq_iff.mp hz
    simp [LinearMap.map_smul, hz']
  let i : K →ₗ[𝓞 K] L :=
    ((LinearMap.toSpanSingleton K _ (e x)).restrictScalars (𝓞 K)).codRestrict L hm
  letI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
  letI : Module.Finite (𝓞 K) K := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective K (fun hzero => hx0 (e.map_eq_zero_iff.mp hzero))
      (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField K
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))


theorem mem_genus_of_isUnimodular : ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.TypeAsm.Std D large₂ → ∀ (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 := by
  intro D large₂ hS _ _ Λ hΛ hU
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := (GlobalTheory.TypeAsm.hostC D large₂ hS).1

  have hloc : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT L ↔
        ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt (VS D).hT P L) :=
    fun L hL => (Formalism.HermitianLatticesTheory.locDual (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT (VS D).herm
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).2
  have hΛfull := full_of_unimodular (VS D).hT (VS D).herm hΛ hU
  have hL0full := full_of_unimodular (VS D).hT (VS D).herm
    (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular
  refine ⟨hΛfull, fun P hP => ?_⟩

  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt D.host.E (VS D).V (VS D).hT hCM (VS D).herm
    (VS D).nondeg (VS D).L0 Λ hL0full hΛfull P hP
    ((hloc _ (VS D).standardTuple_isLattice).1 (VS D).baseLattice_isUnimodular P hP) ((hloc Λ hΛ).1 hU P hP)

end GlobalTheory.RowsOrb.ExGenus
end

