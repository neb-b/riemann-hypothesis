module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestInOpen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : z ∈ U₀) :
    ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => (RatModel.Lat.mem_const_iff M).1 (by
    rw [RatModel.Lat.const_E, ← hB.ee.1 z hc, Q.basis l z hl]
    exact Submodule.subset_span ⟨a, rfl⟩)
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G_of_mem [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hc : Q.P.hom w ∈ U₀) : w ∈ Q.G := by
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inr hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_bot (hB.gen _ hc), Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem big_of_big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isLocalHom_j (u : ρ.UTest p y₀) : IsLocalHom u.j := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ a) * b = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at hb'
  obtain ⟨c, hc⟩ := (u.norm_le (algebraMap u.V _ a)⁻¹).1 (by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ h0, map_one]

theorem mem_range_or (u : ρ.UTest p y₀) (s : Sp u.V) :
    s ∈ Set.range (jK u.V) ∨ s ∈ Set.range (rPt p ≫ spMap u.j) := by
  by_cases h : s.asIdeal = ⊥
  · refine Or.inl ⟨(⊥ : PrimeSpectrum (FractionRing u.V)), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective u.V (FractionRing u.V))
  · have := isLocalHom_j u
    refine Or.inr ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    have e₁ : rPt p (IsLocalRing.closedPoint (kb p)) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    have e₂ : spMap u.j (cPt p) = IsLocalRing.closedPoint u.V := IsLocalRing.comap_closedPoint u.j
    refine ((congrArg (spMap u.j) e₁).trans e₂).trans ?_
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h s.isPrime)).symm

theorem top_le_preimage_G : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x _
  rcases mem_range_or t.u (t.u.G.hom x) with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine mem_G_of_mem hB Q _ ?_
    have e₁ : Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) = c.yV (t.u.G.hom x) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, tm.f_over, Scheme.Hom.comp_apply]
    have e₂ : c.yV (jK t.u.V s) = U₀.ι (c.yK s) := by
      rw [← Scheme.Hom.comp_apply, ← c.yK_fac, Scheme.Hom.comp_apply]
    show Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) ∈ U₀
    rw [e₁, ← hs, e₂]
    exact (c.yK s).2
  · haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
    have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
    obtain ⟨x', rfl, -⟩ := Scheme.exists_preimage_of_isPullback pb x s hs.symm
    have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback pb t.mod.smooth
    have : Smooth t.mod.Φ.G.hom := SmoothOfRelativeDimension.smooth S.g _
    have : JacobsonSpace t.mod.Φ.G.left := LocallyOfFiniteType.jacobsonSpace t.mod.Φ.G.hom
    have hcov := (_root_.GlobalTheory.ZH.ClosedImm.immBy_weight_zero hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol (big_of_big ρ hS)
      t.mod.good t.mod.dim).1
    let U : t.mod.Φ.G.left.Opens := t.mod.r ⁻¹ᵁ ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G)
    by_contra hx
    obtain ⟨a, haU, ha⟩ := nonempty_inter_closedPoints (Z := (U : Set t.mod.Φ.G.left)ᶜ) ⟨x', hx⟩
      U.isOpen.isClosed_compl.isLocallyClosed
    let x₀ := pointOfClosedPoint (K := kb p) t.mod.Φ.G.hom a ha
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := pointOfClosedPoint_comp _ a ha
    have h₃ : x₀ (IsLocalRing.closedPoint (kb p)) = a := pointOfClosedPoint_apply _ a ha _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hmem : x₀ (IsLocalRing.closedPoint (kb p)) ∈
        ⨆ i ∈ {i | t.mod.xe.symm (t.cls i) = 0}, Out.nonzeroLocus (t.mod.F i) := by
      rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hmem
    obtain ⟨i, hi, hm⟩ := hmem
    have h₄ := ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff _ _).2 hm)).ne_zero
    have h₁ : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
      rw [Category.assoc, pb.w, ← Category.assoc, h₂]
      exact Category.id_comp _
    have hcr := tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v
      (h₁.trans (Spec.map_comp _ _).symm) (t.mod.red (Over.homMk x₀ h₂) v hv)
    have hov : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
      rw [Category.assoc, tm.f_over, ← Category.assoc, h₁, Category.assoc, c.fac]
    have key := (_root_.GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2
      ⟨i, t.mod.xe.symm.map_eq_zero_iff.1 hi, h₄⟩
    refine haU ?_
    rw [← h₃]
    exact key (x := IsLocalRing.closedPoint (kb p)) trivial

end GlobalTheory.ZH.TestInOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_cancel {ψ ψ' : Sp (OO p) ⟶ u.D.toPre.P.A.left} (h : gPt p ≫ ψ = gPt p ≫ ψ') : ψ = ψ' := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem gtN_zero (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (hc : c ≫ u.G.hom = spMap u.j)
    (h : u.Lev c g) : u.GtN g 0 := by
  obtain ⟨b₀, hb, H⟩ := h
  intro J hJ χ
  obtain ⟨ce, hce⟩ := exists_level_point u c hc 0
  obtain ⟨hbe, H⟩ := H 0 ce hce
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  have hb₀ : b₀ ≫ u.D.toPre.P.A.hom = spMap u.j := by
    refine ext_of_isDominant (gPt p) ?_
    rw [← Category.assoc, hb]
    refine (Over.w g.b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have ht : ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt 0).pG χ)
      (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) := fun y _ => Set.mem_iInter.2 fun i => by
    have h1 := hJ (b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (by rw [Category.assoc, Oφ_over, hb₀])
    rw [← Category.assoc, hb, ← gtφ_eq] at h1
    exact (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _) (level_Oφ u b₀ ce hbe χ i)).mpr (top_le_comp h1 _ trivial)
  obtain ⟨x, hx, hx'⟩ := H χ _ ht
  rw [← hx, norm_eq_one_of_isUnit u (e := 0) (by rw [hx']; exact isUnit_valR _ _ ht _)]
  simp

theorem parAt [ArithBase o Ω] (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC)
    (hc : c ≫ u.G.hom = spMap u.j) (ha : gPt p ≫ c = u.toG a) (h : u.Lev c g) (k : ℕ) : u.ParAt k a g := by
  obtain ⟨b₀, hb, H⟩ := h
  intro w hw l hl
  choose ce hce using exists_level_point u c hc
  have hbe := fun e => (H e (ce e) (hce e)).1
  choose d hd using fun y => exists_chart u.D.toPre.P.isLB y
  obtain ⟨jL, hjL⟩ := exists_chart u.U.LG.isLB (c (cpt _))
  have hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL := (top_le_iff_cpt _ _).2 hjL
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨ω, ωe, hω0, hω, hωe⟩ := exists_omega u c b₀ ce hce hbe hL hM hc
  have hθ : ∀ θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left,
      ⊤ ≤ (b₀ ≫ θ) ⁻¹ᵁ u.D.toPre.P.L.U (d ((b₀ ≫ θ) (cpt _))) := fun θ => (top_le_iff_cpt _ _).2 (hd _)
  choose x hx hx' using fun e χ => (H e (ce e) (hce e)).2 χ (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))
    (fun y _ => Set.mem_iInter.2 fun i => (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _)
      (level_Oφ u b₀ (ce e) (hbe e) χ i)).mpr (top_le_comp (hθ _) _ trivial))
  have hx0 : ∀ e χ, x 0 χ = x e χ := fun e χ => Subtype.ext ((hx 0 χ).trans (hx e χ).symm)
  have HS := fun σ f hE => hasSum_integral u c b₀ ce hce hbe hL d hd (x 0) (fun e χ => by rw [hx0 e, hx']) ω ωe hω hωe
    (k := k) σ f hE
  let z : Sp (PadicAlgCl p) := cpt _
  obtain ⟨J, hJ, eJ⟩ := exists_good u.D.toPre.P.L u.D.toPre.P.isLB z
    (fun θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left => gPt p ≫ b₀ ≫ θ) (fun θ => d ((b₀ ≫ θ) (cpt _)))
    (fun θ θ' e => by rw [gPt_cancel u e]) (fun θ => top_le_comp (hθ θ) _ trivial)
  let r : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hr : r ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = gPt p ≫ c := by
    rw [ha, ← Category.assoc]
    exact congrArg (fun t : u.PtC => t.left ≫ _) (lift_snd _ _)
  have hr' : r ≫ (fst (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
  obtain ⟨τ, τ0, hτ⟩ := exists_valF_secLin u.U.LG.isLB _ _ r hr' (gPt p ≫ c) hr k (l := l) (l' := jL)
    (by rw [ha]; exact hl) (top_le_comp hL _)
  obtain ⟨κ, κ0, hκ⟩ := exists_coef_secLin u.D.toPre (PadicAlgCl p) k g w hw z J hJ
  refine ⟨κ * ω ^ k * τ⁻¹, by simp [τ0, κ0, hω0], ?_⟩
  rintro σ' s ⟨n, cc, σ, f, hE, hσ, hs⟩
  have e₁ : valF r _ (σ'.f (fun _ => l)) =
      τ * ∑ i, cc i * ((secVal u.U.toUnifPre (σ i) c jL : OO p) : PadicAlgCl p) :=
    (hτ σ' n cc σ hσ).trans (congrArg (τ * ·) (Finset.sum_congr rfl fun i _ => congrArg (cc i * ·)
      (valR_spMap (OO p).subtype c _ (top_le_secChart hL) _)))
  have e₂ : ∀ χ, coef s g w χ = κ * ∑ i, cc i *
      ((valR b₀ _ ((f i χ).f (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) * x 0 χ : OO p) : PadicAlgCl p) := by
    intro χ
    refine (hκ s χ n cc (fun i => f i χ) (hs χ) (gPt p ≫ b₀) (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))
      (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _))) hb (fun i => by rw [Category.assoc, eJ])
      (fun i => by rw [Category.assoc, eJ])).trans (congrArg (κ * ·) (Finset.sum_congr rfl fun i _ =>
        congrArg (cc i * ·) ?_))
    rw [MulMemClass.coe_mul]
    exact congrArg₂ (· * ·) (valR_spMap (OO p).subtype b₀ _
      ((top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun j => hd ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) _) (hx 0 χ).symm
  have hs' := (hasSum_sum (s := Finset.univ) fun i _ => (HS (σ i) (f i) (hE i)).mul_left (cc i)).mul_left κ
  show HasSum _ (_ * valF r _ (σ'.f (fun _ => l)))
  rw [e₁, funext e₂]
  refine (congrArg (HasSum _ ·) ?_).mp hs'
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem gtN_zero_and_parAt : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ u c g a hc ha h => ⟨gtN_zero u c g hc h, fun k _ => parAt u c g a hc ha h k⟩

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnifPullbackOfUnifRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH

theorem exists_sec_pull_of_comp {X Y Z : Scheme.{0}} (L : LB X) (j : Y ⟶ X) (n : Z ⟶ Y) (φ : Z ⟶ X) (e : n ≫ j = φ)
    (σ : LB.Sec (L.pull j)) : ∃ θ : LB.Sec (L.pull φ), ∀ y, n y ∈ nonzeroLocus σ → y ∈ nonzeroLocus θ := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : PUnit => j) (fun _ => 1) σ n, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : y ∈ Z.basicOpen ((n.app _).hom (σ.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  have h₂ : y ∈ (L.pull (n ≫ j)).U k := mem_pull.2 ((mem_pull (F := j)).1 (Y.basicOpen_le _ hk))
  exact (Z.basicOpen_res _ _).ge ⟨h₂, h₁⟩

theorem unif_pullback_of_unif_ring : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (W : (Sp R).Opens), IsSemiAbelian G → L.IsSymmetric → HypS G L.L → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G)) → (∃ θ : LB.Sec L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R) → (W : Set (Sp R)).Nonempty → (W : Set (Sp R)) = abLocus G → IsProper (pullback.snd G.hom W.ι) → RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = L ∧ ∀ y, PsiUnitOn D.toPre y W) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → IsOpen (abLocus Q.G) → Q.Ab → Q.LocTheta → HypS Q.G Q.L.L → (∀ W : M.Z.Opens, (W : Set M.Z) ⊆ abLocus Q.G → RelAmple ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι)) ∧ KTriv ((Over.pullback W.ι).obj Q.G) (Q.L.L.pull (pullback.fst Q.G.hom W.ι))) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (ξ : Sp R ⟶ M.Z), (ξ ⁻¹' abLocus Q.G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj Q.G)], ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (IsLocalRing.maximalIdeal R) D A ((Over.pullback ξ).obj Q.G)), LBIso U.LG.L (Q.L.L.pull (pullback.fst Q.G.hom ξ)) ∧ ∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Q.G) := by
  intro H o Ω _ _ _ _ S ρ M U₀ Q _ hop hab hth hS hpol R _ _ _ _ hN hI hC ξ hne _
  have semiPull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G],
      IsSemiAbelian G → IsSemiAbelian ((Over.pullback f).obj G) := by
    intro S S' f G _ hG
    refine
      { comm := ?_
        smooth := ?_
        separated := ?_
        quasiCompact := ?_
        geomConnected := ?_
        fibres := ?_ }
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro K _ _ q
      obtain ⟨E⟩ := hG.fibres K (q ≫ f)
      let eM := (Functor.mapMonNatIso (Over.pullbackComp q f) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ f)).obj G ≅ (Over.pullback q).obj ((Over.pullback f).obj G) :=
        (Mon.forget _).mapIso eM
      haveI : IsMonHom e.hom := by
        change IsMonHom eM.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      haveI : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
      exact ⟨{
        X := E.X
        addCommGroup := E.addCommGroup
        free := E.free
        finite := E.finite
        B := E.B
        grpB := E.grpB
        isAbelian := E.isAbelian
        q := e.inv ≫ E.q
        q_hom := inferInstance
        q_flat := by rw [Over.comp_left]; have := E.q_flat; infer_instance
        q_surjective := by rw [Over.comp_left]; have := E.q_surjective; infer_instance
        q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; infer_instance
        i := E.i ≫ e.hom
        i_hom := inferInstance
        isKernel := by
          refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have h := isGrpPullback_pullback Q.G ξ
  obtain ⟨hL, hr, ⟨c', -⟩, hs⟩ := CubePf.cubePull _ _ Q.G _ (cubeMapOf h) Q.L Q.cub
  have hrefl : LBIso (Q.L.L.pull (pullback.fst Q.G.hom ξ)) (Q.L.L.pull (pullback.fst Q.G.hom ξ)) :=
    ⟨_, CubePf.idIsoL_isGen hL⟩
  let W₀ : M.Z.Opens := ⟨abLocus Q.G, hop⟩
  let W : (Sp R).Opens := ξ ⁻¹ᵁ W₀
  let G' := (Over.pullback ξ).obj Q.G
  have h₀ := isGrpPullback_pullback Q.G W₀.ι
  have h₁ := isGrpPullback_pullback G' W.ι
  have sq : (ξ ∣_ W₀) ≫ W₀.ι = W.ι ≫ ξ := morphismRestrict_ι ξ W₀
  have h₂ := (h₁.comp h).congr sq.symm rfl
  let ψ : ((Over.pullback W.ι).obj G').left ⟶ ((Over.pullback W₀.ι).obj Q.G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst Q.G.hom W₀.ι = pullback.fst G'.hom W.ι ≫ pullback.fst Q.G.hom ξ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback W.ι).obj G') ((Over.pullback W₀.ι).obj Q.G) (ξ ∣_ W₀) ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hsa := semiPull W₀.ι Q.G Q.semi
  have hA : IsAbelianScheme ((Over.pullback W₀.ι).obj Q.G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := hab.2 W₀ subset_rfl, geomConnected := hsa.geomConnected }
  have hiso : LBIso ((Q.L.L.pull (pullback.fst Q.G.hom ξ)).pull (pullback.fst G'.hom W.ι))
      ((Q.L.L.pull (pullback.fst Q.G.hom W₀.ι)).pull ψ) :=
    LBIso.chartPull
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => pullback.fst G'.hom W.ι) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => (Category.comp_id _).symm)
      (chartPullLinComb Q.L.L _ (fun _ : PUnit => ψ) (fun _ => 𝟙 _) (fun _ => 1) _
        fun _ => hψ.trans (Category.comp_id _).symm)
      ⟨_, CubePf.idIsoL_isGen (pull_isLB Q.L.isLB (𝟙 _))⟩
  obtain ⟨hA', ha, hk⟩ := GlobalTheory.pol_pull _ _ _ _ _ ψ _ _ (pull_isLB Q.L.isLB _) (pull_isLB hL _) hA h₃ hiso
  obtain ⟨ha₀, hk₀⟩ := hpol W₀ subset_rfl
  have hsp : ∃ E : SplitExt (Sp (IsLocalRing.ResidueField R)),
      E.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj G') := by
    obtain ⟨E, hE⟩ := GlobalTheory.ZJ.SplitAll.fieldPoint (G := Q.G) Q.split _ (spMap (IsLocalRing.residue R) ≫ ξ)
    exact ⟨E, isGt_of_iso (pullCompIso _ ξ Q.G) hE⟩
  have hθ' : ∃ θ : LB.Sec (Q.L.L.pull (pullback.fst Q.G.hom ξ)), ∃ x ∈ nonzeroLocus θ,
      G'.hom x = IsLocalRing.closedPoint R := by
    obtain ⟨N, σ, hz, hσ⟩ := hth (ξ (IsLocalRing.closedPoint R))
    have hξ : ξ ⁻¹ᵁ N = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem ξ hz
    obtain ⟨n, hn⟩ : ∃ n : G'.left ⟶ (Q.G.hom ⁻¹ᵁ N).toScheme, n ≫ (Q.G.hom ⁻¹ᵁ N).ι = pullback.fst Q.G.hom ξ :=
      ⟨IsOpenImmersion.lift _ (pullback.fst Q.G.hom ξ) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ N) h.1.w).mpr (hξ.ge (Set.mem_univ (G'.hom y)))),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨θ, hθ⟩ := exists_sec_pull_of_comp Q.L.L _ n _ hn σ
    obtain ⟨x, hx, hx'⟩ := hσ _ hz
    obtain ⟨y, hy, hy'⟩ := Scheme.exists_preimage_of_isPullback h.1 _ _ hx'
    refine ⟨θ, y, hθ y ?_, hy'⟩
    have e : n y = x := (Q.G.hom ⁻¹ᵁ N).ι.isOpenEmbedding.injective
      ((congrArg (fun q => q y) hn).trans hy)
    rwa [e]
  obtain ⟨D, A, U, hU, hP⟩ := H R hN hI hC G' ((cubeMapOf h).rigLB Q.L hL hr) c' W
    (semiPull ξ Q.G Q.semi) (hs Q.sym)
    (GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.G G' ξ _ Q.L.L _ Q.L.isLB hL h hrefl hS) hsp hθ' hne
    (Set.ext fun x => abLocus_pullback abLocusOne Q.semi h.1 x) hA'.proper
    (ha ha₀) (hk hk₀)
  exact ⟨D, A, U, by rw [hU]; exact hrefl, hP⟩

end GlobalTheory.ZH

end
end

