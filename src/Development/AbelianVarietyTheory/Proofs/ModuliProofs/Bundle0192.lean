module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV

namespace GlobalTheory.EmbCut

theorem powIsLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem isoPullAlong {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L j j rfl) (Geo.Tor.chartPullPull M j j rfl) h

theorem symB_of_iso {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hs : SymB L)
    {Y : Scheme.{0}} (e : Y ≅ A.left) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) :
    SymB (A := A) (M.pull e.inv) := by
  have h1 : LBIso (M.pull e.inv) (lbPow L N) :=
    LBIso.chartPull (Geo.Tor.chartPullPull M e.inv e.inv rfl) (Geo.Tor.chartPullSec _ e.hom e.inv e.inv_hom_id) h
  have hN := powIsLB hL N
  have hM' := LB.isLB_pull hM e.inv
  obtain ⟨-, a, -, -, c, -⟩ := _root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K A.left A.hom L hL
  exact LBIso.trans hM' hN (LB.isLB_pull hM' _) h1 (LBIso.trans hN (LB.isLB_pull hN _) (LB.isLB_pull hM' _)
    (LBIso.trans hN (powIsLB (LB.isLB_pull hL _) N) (LB.isLB_pull hN _) ((a _ (LB.isLB_pull hL _) hs).2 N) (c _ _ N))
    (isoPullAlong h1.symm _))

theorem sectionsHaveFiniteDimension_of_iso_pulled_pow {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB)
    (e : Y ≅ X) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) (n r : ℕ)
    (hr : SectionsHaveFiniteDimension p (lbPow L (N * n)) r) : SectionsHaveFiniteDimension (e.hom ≫ p) (lbPow M n) r := by
  have hN := powIsLB hL N
  have h1 : SectionsHaveFiniteDimension p (lbPow (lbPow L N) n) r :=
    ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K X p _ (powIsLB hL (N * n))).2.1 _ (powIsLB hN n)
      ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K X p L hL).2.2.1 N n).symm).1 r hr
  have h2 := ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K X p _ (powIsLB hN n)).2.2.2.2.2 Y e r).1 h1
  have h3 : LBIso (lbPow M n) ((lbPow (lbPow L N) n).pull e.hom) :=
    LBIso.trans (powIsLB hM n) (powIsLB (LB.isLB_pull hN _) n) (LB.isLB_pull (powIsLB hN n) _)
      (((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y (e.hom ≫ p) M hM).2.1 _ (LB.isLB_pull hN _) h).2 n)
      ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K X p _ hN).2.2.2.2.1 Y e.hom n)
  exact ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K Y (e.hom ≫ p) _ (LB.isLB_pull (powIsLB hN n) _)).2.1 _ (powIsLB hM n) h3.symm).1 r h2

end GlobalTheory.EmbCut

namespace GlobalTheory


open EmbCut in
theorem cutBy_embedded_abelian : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  intro H H2 g J _ Mat κ n hn hodd
  have hn2 := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, hd⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H H2 g ((n ^ 2) ^ 2) (Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdvd' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  obtain ⟨Q, hQ⟩ := hd _ le_rfl (Ix g ((n ^ j) ^ 2)) (fun a i => ZMod.castHom hdvd' (ZMod ((n ^ 2) ^ 2)) (a i))
    (fun c => by
      choose a ha using fun i => ZMod.castHom_surjective hdvd' (c i)
      exact ⟨a, funext ha⟩)
  refine ⟨Ix g ((n ^ j) ^ 2), inferInstance, id, Q, d, fun K _ _ β t σ p hE hp => ?_⟩
  obtain ⟨hiso, hM, hV, hL, hmod, -, hlab⟩ := _root_.GlobalTheory.embSec_veryAmple_periodic H H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (by nlinarith) hE
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    pullback.condition.symm.trans (Category.comp_id _)
  have hk : ((n ^ j : ℕ) : K) ≠ 0 := fun h => by
    have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow, h] at this
    exact this (by simp)
  have key := hQ K t.pol rfl _ e _ σ (n ^ j) _ (fun h => t.lab h ^ n ^ j) p hM
    (symB_of_iso t.isLB (_root_.GlobalTheory.principal_polarisation_numerics H H2 K t.pol).2.2.1 e hM _ hL) (he.symm ▸ hV)
    (fun a a' h => hmod a a' fun i => by
      have := congrFun h i
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [ZMod.castHom_apply, ZMod.natCast_val] using this)
    (fun m hm => sectionsHaveFiniteDimension_of_iso_pulled_pow t.A.hom t.isLB e hM _ hL m _ (by
      rw [← mul_pow]
      exact PowSec.exists_basis_sections H.globalSectionsRank K t.pol _ (Nat.mul_pos (by positivity) hm)))
    ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn2).le) hk hlab
    (fun h => by
      have : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := by
        rw [Iso.comp_inv_eq]
        exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j))).symm
      exact this.symm ▸ hp h)
  exact he ▸ key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBirationalModelSemiAbelianAmpleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.TripleGlue

def DensePart {X X₀ : Scheme.{0}} (j : X₀ ⟶ X) : Prop :=
  (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) ∧ IsPreimmersion j ∧ Flat j ∧
    IsDominant j ∧ QuasiCompact j

theorem DensePart.restrict {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) (i : Y ⟶ X) [IsOpenImmersion i]
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) : DensePart k := by
  obtain ⟨⟨hn, z, hz₁, hz₂⟩, h₁, h₂, h₃, h₄⟩ := h
  have sq : IsPullback (𝟙 X₀) k j i := IsPullback.of_horiz_isIso_mono ⟨by rw [hk, Category.id_comp]⟩
  refine ⟨⟨fun y => ?_, i ≫ z, inferInstance, inferInstance⟩, MorphismProperty.of_isPullback sq h₁,
    MorphismProperty.of_isPullback sq h₂, ⟨?_⟩, MorphismProperty.of_isPullback sq h₄⟩
  · obtain ⟨_, _⟩ := hn (i y)
    have e := (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · have e : Set.range k = i ⁻¹' Set.range j := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hk, Scheme.Hom.comp_apply]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, i.isOpenEmbedding.injective (by rw [← hx, ← hk, Scheme.Hom.comp_apply])⟩
    rw [DenseRange, e]
    exact j.denseRange.preimage i.isOpenEmbedding.isOpenMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_fac {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {t₀ : SAB H X₀} {t : SAB H X} (a : SABMap t₀ t j) (i : Y ⟶ X)
    {k : X₀ ⟶ Y} (hk : k ≫ i = j) :
    ∃ (s : SAB H Y) (b : SABMap t₀ s k) (m : SABMap s t i), b.φ ≫ m.φ = a.φ := by
  obtain ⟨_, _, _, _, _, m, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabPull Out.CubePf.cubePull i t
  obtain ⟨a', ha'⟩ := exists_cast a hk.symm
  obtain ⟨b, hb⟩ := ObjMaps.exists_sab_cancel m a'
  exact ⟨_, b, m, hb.symm.trans ha'⟩

theorem DensePart.generic {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} {t : SAB H X}
    (a : SABMap t₀ t j) (hp : IsProper t₀.G.hom) : IsReduced X ∧ genericPoints X ⊆ abLocus t.G := by
  obtain ⟨hX, h₁, h₂, h₃, h₄⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX.1 x).1
    infer_instance
  exact ⟨isReduced_of_isReduced_stalk X,
    (densePart_basic X X₀ j h₁ h₂ h₃ h₄).1.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩

section

variable (hdvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
include hdvr

theorem DensePart.exists_map {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} {k : X₀ ⟶ Y} (h : DensePart k) {i : Y ⟶ X}
    (hk : k ≫ i = j) {t₀ : SAB H X₀} {t : SAB H X} {s : SAB H Y} (a : SABMap t₀ t j) (b : SABMap t₀ s k)
    (hp : IsProper t₀.G.hom) : ∃ n : SABMap s t i, b.φ ≫ n.φ = a.φ := by
  obtain ⟨s', b', m, hm⟩ := exists_fac a i hk
  obtain ⟨c, hc⟩ := exists_sabMap_id_of_common_generic hdvr E H Y X₀ k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    t₀ s s' b b' hp
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m c
  obtain ⟨n', hn'⟩ := exists_cast n (Category.id_comp i)
  exact ⟨n', by rw [hn', hn, ← Category.assoc, hc, hm]⟩

theorem DensePart.glue_top {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {U V : X.Opens} (hUV : U ⊔ V = ⊤)
    {jU : X₀ ⟶ U.toScheme} {jV : X₀ ⟶ V.toScheme} (hU : jU ≫ U.ι = j) (hV : jV ≫ V.ι = j) {t₀ : SAB H X₀}
    {t₁ : SAB H U.toScheme} {t₂ : SAB H V.toScheme} (a₁ : SABMap t₀ t₁ jU) (a₂ : SABMap t₀ t₂ jV)
    (hp : IsProper t₀.G.hom) : ∃ t : SAB H X, Nonempty (SABMap t₀ t j) := by
  have hr : Set.range j ⊆ Set.range (U ⊓ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨by rw [← hU]; exact (jU x).2, by rw [← hV]; exact (jV x).2⟩
  obtain ⟨k, hk⟩ : ∃ k : X₀ ⟶ (U ⊓ V).toScheme, k ≫ (U ⊓ V).ι = j := ⟨_, IsOpenImmersion.lift_fac _ j hr⟩
  have hkU : k ≫ X.homOfLE inf_le_left = jU := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hk, hU]
  have hkV : k ≫ X.homOfLE inf_le_right = jV := by
    rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, hk, hV]
  obtain ⟨s, b, m₁, -⟩ := exists_fac a₁ _ hkU
  obtain ⟨m₂, -⟩ := (h.restrict _ hk).exists_map hdvr hkV a₂ b hp
  obtain ⟨t, n₁, -, -⟩ := _root_.GlobalTheory.TripleGlue.exists_sab_glue E H X U V t₁ t₂ s m₁ m₂ hUV ((h.restrict _ hU).generic a₁ hp)
    ((h.restrict _ hV).generic a₂ hp)
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n₁ a₁
  obtain ⟨n', -⟩ := exists_cast n hU
  exact ⟨t, ⟨n'⟩⟩


omit hdvr in
theorem exists_trace {X X₀ Y : Scheme.{0}} {j : X₀ ⟶ X} (i : Y ⟶ X) {k : X₀ ⟶ Y} (hk : k ≫ i = j) {U : X.Opens}
    {jU : X₀ ⟶ U.toScheme} (hU : jU ≫ U.ι = j) {t₀ : SAB H X₀} {t : SAB H U.toScheme} (a : SABMap t₀ t jU) :
    ∃ (k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme) (s : SAB H (i ⁻¹ᵁ U).toScheme),
      k' ≫ (i ⁻¹ᵁ U).ι = k ∧ Nonempty (SABMap t₀ s k') := by
  have hr : Set.range k ⊆ Set.range (i ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show i (k x) ∈ U
    rw [← Scheme.Hom.comp_apply, hk, ← hU]
    exact (jU x).2
  obtain ⟨k', hk'⟩ : ∃ k' : X₀ ⟶ (i ⁻¹ᵁ U).toScheme, k' ≫ (i ⁻¹ᵁ U).ι = k := ⟨_, IsOpenImmersion.lift_fac _ k hr⟩
  have e : k' ≫ (i ∣_ U) = jU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk', hk, hU]
  obtain ⟨s, b, -, -⟩ := exists_fac a _ e
  exact ⟨k', s, hk', ⟨b⟩⟩

theorem DensePart.glue_sup {X X₀ : Scheme.{0}} {j : X₀ ⟶ X} (h : DensePart j) {t₀ : SAB H X₀} (hp : IsProper t₀.G.hom)
    {U V : X.Opens}
    (hU : ∃ (k : X₀ ⟶ U.toScheme) (s : SAB H U.toScheme), k ≫ U.ι = j ∧ Nonempty (SABMap t₀ s k))
    (hV : ∃ (k : X₀ ⟶ V.toScheme) (s : SAB H V.toScheme), k ≫ V.ι = j ∧ Nonempty (SABMap t₀ s k)) :
    ∃ (k : X₀ ⟶ (U ⊔ V).toScheme) (s : SAB H (U ⊔ V).toScheme), k ≫ (U ⊔ V).ι = j ∧ Nonempty (SABMap t₀ s k) := by
  obtain ⟨jU, t₁, hU, ⟨a₁⟩⟩ := hU
  obtain ⟨jV, t₂, hV, ⟨a₂⟩⟩ := hV
  have hk : (jU ≫ X.homOfLE le_sup_left) ≫ (U ⊔ V).ι = j := by rw [Category.assoc, Scheme.homOfLE_ι, hU]
  obtain ⟨k₁, s₁, hk₁, ⟨b₁⟩⟩ := exists_trace _ hk hU a₁
  obtain ⟨k₂, s₂, hk₂, ⟨b₂⟩⟩ := exists_trace _ hk hV a₂
  have hc : (U ⊔ V).ι ⁻¹ᵁ U ⊔ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, Scheme.Opens.ι_preimage_self]
  obtain ⟨t, ha⟩ := (h.restrict _ hk).glue_top hdvr hc hk₁ hk₂ b₁ b₂ hp
  exact ⟨_, t, hk, ha⟩

end

end GlobalTheory.TripleGlue

theorem GlobalTheory.exists_sab_glue_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ : Scheme.{0}) (j : X₀ ⟶ X) (t₀ : SAB H X₀) (I : Type) [Finite I] (U : I → X.Opens) (jU : ∀ i, X₀ ⟶ (U i).toScheme) (t : ∀ i, SAB H (U i).toScheme) (a : ∀ i, SABMap t₀ (t i) (jU i)), Nonempty I → (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsProper t₀.G.hom → ⨆ i, U i = ⊤ → (∀ i, jU i ≫ (U i).ι = j) → ∃ (t' : SAB H X) (a' : SABMap t₀ t' j) (n : ∀ i, SABMap (t i) t' (U i).ι), ∀ i, (a i).φ ≫ (n i).φ = a'.φ := by
  intro hdvr E _ _ _ H X X₀ j t₀ I _ U jU t a hI hX h₁ h₂ h₃ h₄ hp hcov hj
  have h : TripleGlue.DensePart j := ⟨hX, h₁, h₂, h₃, h₄⟩
  have := Fintype.ofFinite I
  have key : ∃ (k : X₀ ⟶ (Finset.univ.sup' Finset.univ_nonempty U).toScheme) (s : SAB H _),
      k ≫ (Finset.univ.sup' Finset.univ_nonempty U).ι = j ∧ Nonempty (SABMap t₀ s k) :=
    Finset.sup'_induction (p := fun W : X.Opens => ∃ (k : X₀ ⟶ W.toScheme) (s : SAB H W.toScheme),
      k ≫ W.ι = j ∧ Nonempty (SABMap t₀ s k)) _ _ (fun _ hU _ hV => h.glue_sup hdvr hp hU hV)
      (fun i _ => ⟨jU i, t i, hj i, ⟨a i⟩⟩)
  rw [Finset.sup'_univ_eq_ciSup, hcov] at key
  obtain ⟨k, s, hk, ⟨b⟩⟩ := key
  have e : j ≫ X.topIso.inv = k := by
    rw [← hk, Category.assoc]
    exact (congrArg (k ≫ ·) X.topIso.hom_inv_id).trans (Category.comp_id _)
  obtain ⟨t', a', -, -⟩ := TripleGlue.exists_fac b _ e
  choose n hn using fun i => (h.restrict _ (hj i)).exists_map hdvr (hj i) a' (a i) hp
  exact ⟨t', a', n, hn⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem exists_sabMap_extending : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (C' : Cpt c' t' β') (r : U' ⟶ U) (ν : SABMap t' t r) (f : C'.X ⟶ C.X), IsDedFrac β' → Algebra.FiniteType ℤ O' → IsProper t'.G.hom → C'.j ≫ f = r ≫ C.j → ∃ mu : SABMap C'.t C.t f, C'.m.φ ≫ mu.φ = ν.φ ≫ C.m.φ :=
  exists_sabMap_extending_of_iso GlobalTheory.exists_sabMap_id_of_common_generic

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_laws : Out.Laws → N1c := by
  intro hL
  have hU : ThetaUnifAV :=
    thetaUnifAV_of_laws (by cases hL; assumption) (by cases hL; assumption) (by cases hL; assumption)
      (by cases hL; assumption) (by cases hL; assumption)
  exact _root_.GlobalTheory.familyUnif_of_thetaUnif hU hL

end GlobalTheory
end

