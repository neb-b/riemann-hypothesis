module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

theorem exists_mat {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n n' : ℕ} (hn : n = n')
    (V : Submodule K (Fin n → K)) (V' : Submodule K' (Fin n' → K'))
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    ∃ G : Matrix (Fin (Module.finrank K' V')) (Fin (Module.finrank K V)) K', Function.Bijective G.mulVec ∧
      ∀ y : Fin (Module.finrank K V) → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • (Module.finBasis K' V' l : Fin n' → K')) k' =
          φ ((∑ i, y i • (Module.finBasis K V i : Fin n → K)) k) := by
  subst hn
  classical
  set b := Module.finBasis K V
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  have hrel : ∀ x' : Fin n → K', ∀ x : Fin n → K, (∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)) ↔ x' = Φ x := by
    intro x' x
    constructor
    · intro h; funext k; exact h k k rfl
    · rintro rfl k k' hk; rw [Fin.ext hk]
  have hS : {x' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = Φ '' V := by
    ext x'; simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, ((hrel x' x).1 h).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hrel _ x).2 rfl⟩
  rw [hS] at hV
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by funext k; simp [hΦ]
  have hΦsmul : ∀ (a : K) x, Φ (a • x) = φ a • Φ x := fun a x => by funext k; simp [hΦ]
  have hΦsum : ∀ y : Fin (Module.finrank K V) → K, Φ (∑ i, y i • (b i : Fin n → K)) = ∑ i, φ (y i) • Φ (b i) := by
    intro y
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hΦ, Finset.sum_apply, map_sum]
  let c : Fin (Module.finrank K V) → Fin n → K' := fun i => Φ (b i)
  have hc_mem : ∀ i, c i ∈ V' := fun i => hV ▸ Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  have hli : LinearIndependent K' c := by
    letI := φ.toAlgebra
    have h0 : LinearIndependent K (fun i => (b i : Fin n → K)) := b.linearIndependent.map' V.subtype V.ker_subtype
    exact (linearIndependent_algebraMap_comp_iff).2 h0
  have hspan : Submodule.span K' (Set.range c) = V' := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hc_mem i
    · rw [hV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (⟨x, hx⟩ : V) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
      have hx2 : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Fin n → K) := by
        have := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at this
        simpa only [Submodule.coe_smul] using this
      rw [hx2, hΦsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let cV : Fin (Module.finrank K V) → V' := fun i => ⟨c i, hc_mem i⟩
  have hliV : LinearIndependent K' cV := LinearIndependent.of_comp V'.subtype hli
  have hspV : ⊤ ≤ Submodule.span K' (Set.range cV) := by
    rintro ⟨x, hx⟩ _
    rw [← hspan] at hx
    have : Set.range c = V'.subtype '' Set.range cV := by
      ext z; simp [cV, c]
    rw [this, ← Submodule.map_span] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = ⟨x, hspan ▸ (by rw [this, ← Submodule.map_span]; exact ⟨w, hw, hwx⟩)⟩ := Subtype.ext hwx
    rw [← this]; exact hw
  let bc : Module.Basis (Fin (Module.finrank K V)) K' V' := Module.Basis.mk hliV hspV
  set b' := Module.finBasis K' V'
  refine ⟨Matrix.of fun l i => b'.repr (bc i) l, ?_, ?_⟩
  · have hG : (Matrix.of fun l i => b'.repr (bc i) l).mulVec = fun y => b'.equivFun (bc.equivFun.symm y) := by
      funext y l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, map_sum, mul_comm]
    rw [hG]
    exact b'.equivFun.bijective.comp bc.equivFun.symm.bijective
  · intro y k k' hk
    rw [← Fin.ext hk]
    have e1 : (∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • (b' l : Fin n → K')) =
        ((∑ i, φ (y i) • bc i : V') : Fin n → K') := by
      have : ∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • b' l = ∑ i, φ (y i) • bc i := by
        rw [← b'.sum_repr (∑ i, φ (y i) • bc i)]
        congr 1; funext l; congr 1
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
      have := congrArg Subtype.val this
      simpa [Submodule.coe_sum] using this
    rw [e1]
    have e2 : ((∑ i, φ (y i) • bc i : V') : Fin n → K') = ∑ i, φ (y i) • c i := by
      simp [Submodule.coe_sum, bc, cV]
    rw [e2, ← hΦsum]

theorem lat_coords {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K') {n n' d d' : ℕ}
    (hn : n = n') (b : Fin d → Fin n → K) (b' : Fin d' → Fin n' → K') (hb' : LinearIndependent K' b')
    (G : Matrix (Fin d') (Fin d) K')
    (hG : ∀ y : Fin d → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • b' l) k' = φ ((∑ i, y i • b i) k))
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x ∈ M, x ∈ Submodule.span K (Set.range b))
    (M' : Submodule (𝓞 K') (Fin n' → K'))
    (hM' : M' = Submodule.span (𝓞 K') {x' | ∃ x ∈ M, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    M'.comap ((Fintype.linearCombination K' b').restrictScalars (𝓞 K')) =
      Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K))) := by
  subst hn
  set L' := (Fintype.linearCombination K' b').restrictScalars (𝓞 K') with hL'
  have hL'apply : ∀ c, L' c = ∑ l, c l • b' l := fun c => by
    simp [hL', Fintype.linearCombination_apply]
  have key : ∀ y : Fin d → K, L' (G.mulVec fun i => φ (y i)) = fun k => φ ((∑ i, y i • b i) k) := by
    intro y; funext k; rw [hL'apply]; exact hG y k k rfl
  have hinj : Function.Injective L' := by
    intro c₁ c₂ h
    rw [hL'apply, hL'apply] at h
    have h0 : ∑ l, (c₁ - c₂) l • b' l = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext l
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb' _ h0 l)
  apply le_antisymm
  · intro c hc
    have hc' : L' c ∈ M' := hc
    have hle : M' ≤ (Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K)))).map L' := by
      rw [hM', Submodule.span_le]
      rintro x' ⟨x, hx, hrel⟩
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hM x hx)
      have hyM : y ∈ M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) := by
        show (Fintype.linearCombination K b) y ∈ M
        rw [Fintype.linearCombination_apply, hy]; exact hx
      have : x' = L' (G.mulVec fun i => φ (y i)) := by
        rw [key y, hy]; funext k; exact hrel k k rfl
      rw [this]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hyM, rfl⟩)
    obtain ⟨e, he, hec⟩ := hle hc'
    rw [← hinj hec]; exact he
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show L' (G.mulVec fun i => φ (y i)) ∈ M'
    rw [hM', key y]
    refine Submodule.subset_span ⟨∑ i, y i • b i, ?_, fun k k' hk => by rw [Fin.ext hk]⟩
    have : (Fintype.linearCombination K b) y ∈ M := hy
    rwa [Fintype.linearCombination_apply] at this

theorem complexPoints_baseLevelLift_readAtBaseEmbedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    @Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y)) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k) := by
  have hpos : (0:ℝ) < RealDat.nP F.lv2 false := by
    unfold RealDat.nP; exact_mod_cast Nat.card_pos
  set s := twAt D.what₂.embLL A3.A.v0
  set WS := R.toRealDat.WS F.lv2 false i (sg0 D A3.A)
  have h2 : (@Tw.out s WS ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) =
      ∑ k, cj s (cpt A3.fam3.base3.v0.embedding y k) • (⟨R.toRealDat.bC F.lv2 false i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ : WS) := by
    simp only [CxData.wC, lin, Fintype.linearCombination_apply]
    rfl
  have h1 : ∀ x : Tw s WS, @Tw.out s _ ((R.toCx3 F).eW false i x) = (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((Tw.out x : WS) : (R.HW i (sg0 D A3.A)).H) := fun x => rfl
  refine Eq.trans (h1 ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, Submodule.coe_sum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, map_smulₛₗ, smul_comm]
  have he : cj s (cpt A3.fam3.base3.v0.embedding y k) = sg0 D A3.A (y k) := by
    show cj s (A3.A.v0.embedding (y k)) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 (y k), cj_cj]
  rw [he]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k)) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one, one_smul]

theorem liftWeight_complexPoint_eq_twist {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    HEq ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))
      ((R.FW i).j D.what₂.embLL (∑ k, y k • R.toRealDat.bL F.lv2 false i k)) := by
  have e := complexPoints_baseLevelLift_readAtBaseEmbedding R F i y
  have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.hv0
  have key : ∀ (σ σ' : D.what₂.LL →+* ℂ), σ = σ' → ∀ v, HEq ((R.FW i).j σ v) ((R.FW i).j σ' v) := by
    intro σ σ' h v; subst h; rfl
  show HEq (@Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))) _
  rw [e]
  exact key _ _ hs _

theorem nat_eq_of_heq {m m' : ℕ} (hm : m' = m) {f : Fin m → ℕ} {f' : Fin m' → ℕ} (h : HEq f' f) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : f i = f' i' := by
  subst hm
  have := eq_of_heq h
  subst this
  rw [Fin.ext hi]

theorem mem_span_basis {K : Type} [Field K] {n : ℕ} (V : Submodule K (Fin n → K)) [Module.Finite K V] {x : Fin n → K}
    (hx : x ∈ V) : x ∈ Submodule.span K (Set.range fun k => (Module.finBasis K V k : Fin n → K)) := by
  have hx' : (⟨x, hx⟩ : V) = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • Module.finBasis K V i := ((Module.finBasis K V).sum_repr _).symm
  have hx2 : x = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • (Module.finBasis K V i : Fin n → K) := by
    have := congrArg Subtype.val hx'
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  rw [hx2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.Mem.R3.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjEqAddKummerTorusTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KummerConj

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion GlobalTheory.BXOf

attribute [local instance] gtGroup

theorem valuation_val_eq {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (O : ValuationSubring F) (φ : R →+* O)
    (hφ : ∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r))
    {X : Scheme.{0}} {L : LB X} (J₀ : X → L.ι) (h₀ : ∀ x, x ∈ L.U (J₀ x)) {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L (closedPoint F) J) (eJ : ∀ ψ : Sp O ⟶ X, J (spMap O.subtype ≫ ψ) = J₀ (ψ (closedPoint O)))
    {K : Type} [Fintype K] {φs : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φs ε))
    (ht : t.IsGen) (p : K → (Spec (CommRingCat.of R) ⟶ X)) (hp : ∀ k, φs k = jK R ≫ p k) (j : K → L.ι)
    (hj : ∀ k, ⊤ ≤ p k ⁻¹ᵁ L.U (j k)) (h : ⊤ ≤ (LB.LinComb L φs ε).U j) :
    O.valuation (sig F (val t (jFK (R := R) F) (closedPoint F) J) : F) =
      O.valuation (algebraMap (FractionRing R) F (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h)) := by
  have hs : spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R := by
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ
  have hr : ∀ k, jFK (R := R) F ≫ φs k = spMap O.subtype ≫ (spMap φ ≫ p k) := fun k => by
    rw [hp k, ← Category.assoc, ← Category.assoc, hs]
  obtain ⟨w, hw⟩ : ∃ w : ((Sp F).presheaf.stalk (closedPoint F))ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hunit : ∀ (ψ : Sp O ⟶ X) (U : X.Opens) (hU : ψ (closedPoint O) ∈ U) (a : Γ(X, U)ˣ),
      w (gm (spMap O.subtype ≫ ψ) (closedPoint F) U a) = 1 := fun ψ U hU a => by
    refine Units.ext ((hw _).trans ?_)
    rw [← sig_nat O.subtype ψ hU a]
    exact O.valuation_unit _
  have hz : jFK (R := R) F (closedPoint F) ∈ LB.wchart L φs j := h trivial
  have g := gen_trans ht (jFK (R := R) F) (closedPoint F) (hJ.mem φs (jFK (R := R) F)) hz
  have htr : w (trF φs ε (jFK (R := R) F) (closedPoint F) (fun k => J (jFK (R := R) F ≫ φs k)) j) = 1 := by
    show w (∏ k, gm (jFK (R := R) F ≫ φs k) (closedPoint F) (L.U (J (jFK (R := R) F ≫ φs k)) ⊓ L.U (j k))
      (L.g (J (jFK (R := R) F ≫ φs k)) (j k)) ^ ε k) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow]
    refine (congrArg (· ^ ε k) ?_).trans (one_zpow _)
    rw [hr k]
    apply hunit
    exact ⟨by rw [eJ]; exact h₀ _, hj k (show spMap φ (closedPoint O) ∈ ⊤ from trivial)⟩
  have hgv : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) ((LB.LinComb L φs ε).U j)
      (t.s j)).val = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ (closedPoint (FractionRing R))
        trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h).val) := by
    refine (gm_val (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) _ (h trivial) (t.s j)).trans ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h)
      (closedPoint (FractionRing R)) trivial _).symm
  have hsg : sig (FractionRing R) (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R))
      (LB.wchart L φs j) (t.s j)) = GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h := by
    refine Units.ext ((congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom hgv).trans ?_)
    rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
  have n := sig_nat (algebraMap (FractionRing R) F) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (h trivial) (t.s j)
  rw [Category.comp_id] at n
  have n2 := (congrArg (Units.map (algebraMap (FractionRing R) F).toMonoidHom) hsg).symm.trans n
  have e : w (val t (jFK (R := R) F) (closedPoint F) J) =
      w (gm (jFK (R := R) F) (closedPoint F) ((LB.LinComb L φs ε).U j) (t.s j)) := by
    refine (congrArg w g).trans ?_
    rw [map_mul, htr, _root_.one_mul]
    rfl
  rw [← hw, e, hw]
  exact congrArg (fun u : Fˣ => O.valuation (u : F)) n2.symm

theorem conj_eq_add_tor : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  intro R _ _ D hB F _ _ O φ hφ k σ p p' hext hfix
  have hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F :=
    RingHom.ext fun a => σ.commutes a
  obtain rfl : p' = qkExt hB σ.toRingHom hσ' p := (qkExt_iff hB _ hσ' _ _).1 hext
  have hb : extMap σ.toRingHom hσ' ≫ p.g.b = p.g.b := Over.OverMorphism.ext hfix
  set d : GtPtF D F := gtExt D σ.toRingHom hσ' p.g - p.g with hd
  have hdb : d.b = 1 := by
    rw [hd, sub_eq_add_neg, add_b, neg_b, gtExt_b, hb, mul_inv_cancel]
  have hgd : gtExt D σ.toRingHom hσ' p.g = p.g + d := by rw [hd, add_sub_cancel]
  obtain ⟨τ, hτ⟩ := exists_torusPt_eq hdb
  have hkd : k • d = 0 := by
    rw [hd, nsmul_sub, ← map_nsmul, qk_nsmul hB, gtExt_iota, sub_self]
  have hτk : τ ^ k = 1 := by
    have e : torusPt D F (Additive.ofMul (τ ^ k)) = torusPt D F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← hτ, hkd, ofMul_one, map_zero]
    exact Additive.ofMul.injective (torusPt_injective e)
  let q : QkPt D F k := qkMk hB 0 d (by rw [hkd, map_zero])
  refine ⟨τ, q, hτk, rfl, (GlobalTheory.UT.isTor_iff _ _).2 (by
    simpa only [q, qkMk_g] using (isTorusPtF_iff_eq d τ).2 hτ), ?_, fun χ x hx => ?_⟩
  · refine (qkAdd_iff hB _ _ _).2 ?_
    have e : qkAdd hB p q = qkExt hB σ.toRingHom hσ' p := qk_ext (add_zero _) hgd.symm
    rw [e]
    exact qk_equiv_refl hB _

  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB O.subtype Subtype.val_injective J₀ h₀
  let z : (TF (R := R) F).left := closedPoint F
  have hJ' : Good D.P.L z J := hJ
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨w, hw⟩ : ∃ w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ)).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1 := by
    intro Y K _ ψ ε t r
    obtain ⟨u, hu⟩ := val_integral O.subtype h₀ eJ t r
    exact Units.ext ((hw _).trans ((congrArg O.valuation hu).trans (O.valuation_unit u)))
  obtain ⟨b, hb'⟩ := exists_extend O φ ρ rfl p.g.b
  have e₁ := w_nsmul ρ hJ' w hint p.g b hb' χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ'] at e₁
  have face3 (x x' : TF (R := R) F ⟶ D.P.A) : cubV D.cub z J x x' 1 = 1 := by
    have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    refine Eq.trans ?_ ((val_corr (hJ := hJ') (D.cub.face 2) (lift x x').left).trans (val_one _))
    refine Eq.trans ?_ (val_pull (hJ := hJ') ..).symm
    show val D.cub.t (lift x (lift x' 1)).left z J = _
    rw [hm, Over.comp_left]
    all_goals rfl
  refine ⟨(sig F (charVal p.g χ z J) : F), Units.ne_zero _, ?_, ?_⟩
  · have e₂ := congrArg Units.val e₁
    rw [Units.val_pow_eq_pow_val, hw, hw] at e₂
    rw [← e₂]
    obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
    have er : (𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F := by simp
    show O.valuation (sig F (val (D.tau p.y χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) : F) = _
    rw [er]
    refine valuation_val_eq O φ hφ J₀ h₀ hJ eJ (D.tau p.y χ) (tau_isGen D _ _)
      (Sum.elim (Sum.elim (Sum.elim (fun _ => (D.c (p.y + χ)).left) (fun _ => (D.c p.y).left))
        (fun _ => (D.c χ).left)) (fun _ => (η[D.P.A] : _ ⟶ _).left)) ?_ j ?_ h
    · rintro (((_ | _) | _) | _)
      · rfl
      · rfl
      · rfl
      · show (toUnit (TK R)).left ≫ eSec D.P.A = jK R ≫ (η[D.P.A] : _ ⟶ _).left
        have e : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
        rw [e]
        rfl
    · rintro (((_ | _) | _) | _)
      exacts [i1, i2, i3, i4]
  · have key : σ (sig F (charVal p.g χ z J) : F) =
        (sig F (charVal (gtExt D σ.toRingHom hσ' p.g) χ z J) : F) := by
      have e := gtExt_val σ.toRingHom hσ' p.g χ hJ'
      have hφ' : ∀ i, (extMap σ.toRingHom hσ').left ≫ DegPre.gtφ D F p.g.b χ i =
          𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i := by
        intro i
        rw [Category.id_comp]
        fin_cases i
        · show (extMap σ.toRingHom hσ' ≫ (cP D _ χ * p.g.b)).left = (cP D _ χ * p.g.b).left
          rw [MonObj.comp_mul, comp_cP, hb]
        · show (extMap σ.toRingHom hσ' ≫ cP D _ χ).left = (cP D _ χ).left
          rw [comp_cP]
        · show (extMap σ.toRingHom hσ' ≫ p.g.b).left = p.g.b.left
          rw [hb]
        · show (extMap σ.toRingHom hσ' ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
          rw [MonObj.comp_one]
      replace e := e.trans (val_of (p.g.s χ) _ _ J _ (fun i => congrArg J (hφ' i)))
      have n := sig_nat σ.toRingHom (𝟙 (Spec (CommRingCat.of F))) (hJ'.mem (DegPre.gtφ D F p.g.b χ) (𝟙 _))
        ((p.g.s χ).s fun i => J (𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i))
      rw [Category.comp_id] at n
      exact (congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)
    have hs : sig F (charVal d χ z J) = τ (Multiplicative.ofAdd χ) := by
      rw [hτ, torusPt_val τ χ hJ']
      refine Units.ext ?_
      show (stalkClosedPointIso (CommRingCat.of F)).hom.hom (((Sp F).presheaf.germ ⊤ (closedPoint F) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd χ) : F))) = _
      rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
    have e := add_val p.g d χ hJ'
    rw [hdb] at e
    change charVal (p.g + d) χ z J * cubV D.cub z J (cP D _ χ) p.g.b 1 = _ at e
    rw [face3, _root_.mul_one] at e
    rw [key, hgd, e, map_mul, Units.val_mul, hs, mul_comm]

end GlobalTheory.KummerConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActionsOnLiftRulesExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.ActExt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def LevB (D : D7) (i : Fin D.R.m) (Pg : Finset (Pl D.host.E)) (β : ∀ i, GL (Fin (Wc D i).rank) (EAf D)) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (io : La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) (lev : G → La →ₗ[𝓞 D.host.E] La) : Prop :=
  ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
      (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
    ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat (Wc D i) 1,
      finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (Formalism.IndefR.FWT.rank_Wc i)) ∘ₗ io) (lev g a)) -
        (finHom (Wc D i) κ).1.mulVec (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (Formalism.IndefR.FWT.rank_Wc i)) ∘ₗ io) a)) = M • w

theorem act_heq (D : D7) (i : Fin D.R.m) (n : ℕ) {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} {l' : Level H'}
    {c : Coeff l} {c' : Coeff l'} {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {io : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {io' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    {Pg Pg' : Finset (Pl D.host.E)} {β β' : ∀ i, GL (Fin (Wc D i).rank) (EAf D)} {G : Type} [Group G]
    {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r}
    {lev : G → (Dw n).La →ₗ[𝓞 D.host.E] (Dw n).La} {lev' : G → (Dw' n).La →ₗ[𝓞 D.host.E] (Dw' n).La}
    (hH : HEq H' H) (hl : HEq l' l) (hc : HEq c' c) (hD : HEq Dw' Dw) (hX : HEq Xo' Xo) (hi : HEq io' io)
    (hP : HEq Pg' Pg) (hβ : HEq β' β) (he : HEq eG' eG) (hA : l.A = 1)
    (hU : ∀ lev lev' : G → (Dw n).La →ₗ[𝓞 D.host.E] (Dw n).La, LevB D i Pg β eG (io n) l.M (Mfr l) lev →
      LevB D i Pg β eG (io n) l.M (Mfr l) lev' → ∀ g a, lev g a - lev' g a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw n).La))
    (h : LevB D i Pg β eG (io n) l.M (Mfr l) lev) (h' : LevB D i Pg' β' eG' (io' n) l'.M (Mfr l') lev')
    (g g' : G) (hg : HEq g' g) (r : Rul (Xo n) c) (r' : Rul (Xo' n) c') (hr : HEq r' r) :
    HEq (actLev c' (fun g => (lev' g, LinearMap.id)) g' r') (actLev c (fun g => (lev g, LinearMap.id)) g r) := by
  obtain rfl := eq_of_heq hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hX
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hβ
  obtain rfl := eq_of_heq he
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hr
  exact heq_of_eq (congrArg (fun f => f g' r')
    (GlobalTheory.OneMapAllCompare.actLev_congr (lev := fun g => (lev' g, LinearMap.id))
      (lev' := fun g => (lev g, LinearMap.id)) c' hA (hU lev' lev h' h)))

end GlobalTheory.Mem.R3.ActExt
end
end

