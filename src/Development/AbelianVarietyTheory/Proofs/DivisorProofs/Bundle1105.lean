module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.CuspMult GlobalTheory.PRep
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDec

section Abstract

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem mem_fixed {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X} {K : Subgroup H} {x : X} :
    x ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixed, eig]

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ρ : Representation ℂ H V}

theorem isSemisimple (ha : IsAdmissible ρ) (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) {K₀ : Subgroup H}
    (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : ρ.IsSemisimpleRepresentation :=
  _root_.UpperTheory.Reformulated.B.AdmissibleSmoothRepresentations.isSemisimple ha hu ho hc

theorem mem_irrSum {W X : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ H W}
    {ρ : Representation ℂ H X} {C : Submodule ℂ X} (h1 : σ.IsSemisimpleRepresentation) (h2 : IsAdmissible σ)
    {f : W →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 h1
  have hs : σ.asModuleEquiv.symm s ∈ sSup {m : Submodule (MonoidAlgebra ℂ H) σ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ H) m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    trivial
  rw [sSup_eq_iSup'] at hs
  refine Submodule.iSup_induction _ (motive := fun x => f (σ.asModuleEquiv x) ∈ irrSum ρ C) hs ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    obtain ⟨U, rfl⟩ := Subrepresentation.subrepresentationSubmoduleOrderIso.surjective m
    have hU : U.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := hm
      exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U)
    exact GlobalTheory.RepCount.apply_mem_irrSum hU
      (GlobalTheory.RepCount.isAdmissible_of_injective U.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective h2)
      (f := f.comp U.toSubmodule.subtype) ⟨fun s => hf.1 _, fun g s => hf.2 g s⟩ ⟨σ.asModuleEquiv y, hy⟩
  · simp
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem isDecomp_of_form {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (hC : ∀ g, ∀ x ∈ C, ρ g x ∈ C) (B : X → X → ℂ)
    (hl : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z ∧ B y x = star (B x y))
    (hp : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) (hi : ∀ g, ∀ x ∈ C, ∀ y ∈ C, B (ρ g x) (ρ g y) = B x y)
    (hf : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ fixed ρ K))
    {K₀ : Subgroup H} (ho : IsOpen (K₀ : Set H)) (hc : IsCompact (K₀ : Set H)) : IsDecomp ρ C := by
  intro x hx hx'
  let A : Subrepresentation ρ := ⟨C ⊓ smoothPart ρ, fun g v hv => ⟨hC g v hv.1, smoothPart_stable ρ g v hv.2⟩⟩
  have hsym : ∀ x ∈ C, ∀ y ∈ C, B y x = star (B x y) := fun x hx y hy => (hl x hx y hy y hy 0).2
  have h0 : ∀ x ∈ C, B x 0 = 0 := fun x hx => by simpa using (hl x hx 0 C.zero_mem 0 C.zero_mem 1).1
  let cd : InnerProductSpace.Core ℂ A.toSubmodule :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => (hsym _ b.2.1 _ a.2.1).symm
      re_inner_nonneg := fun a => by
        by_cases h : (a : X) = 0
        · simp [h, h0 0 C.zero_mem]
        · exact (hp _ a.2.1 h).le
      add_left := fun a b c => by
        have := (hl _ c.2.1 _ a.2.1 _ b.2.1 1).1
        rw [one_smul, one_mul] at this
        show B (a + b) c = B a c + B b c
        rw [hsym _ c.2.1 _ (C.add_mem a.2.1 b.2.1), this, star_add, hsym _ c.2.1 _ a.2.1, hsym _ c.2.1 _ b.2.1]
      smul_left := fun a b r => by
        have := (hl _ b.2.1 _ C.zero_mem _ a.2.1 r).1
        rw [zero_add, h0 _ b.2.1, zero_add] at this
        show B (r • a) b = star r * B a b
        rw [hsym _ b.2.1 _ (C.smul_mem r a.2.1), this, star_mul', hsym _ b.2.1 _ a.2.1]
      definite := fun a h => by
        by_contra hn
        have := hp _ a.2.1 fun e => hn (Subtype.ext e)
        rw [show B a a = 0 from h] at this
        simp at this }
  have ha : IsAdmissible A.toRepresentation := by
    refine ⟨fun v => ?_, fun K hK _ => ?_⟩
    · have : {g : H | A.toRepresentation g v = v} = {g : H | ρ g v = v} := by
        ext g
        exact Subtype.ext_iff
      rw [this]
      exact v.2.2
    · haveI := hf K hK
      refine FiniteDimensional.of_injective (A.toSubmodule.subtype.restrict (p := fixed A.toRepresentation K)
        (q := C ⊓ fixed ρ K) fun v hv => ⟨v.2.1, fun k => congrArg Subtype.val (hv k)⟩) fun a b h => ?_
      have h' : (a.1 : X) = b.1 := congrArg (fun z : ↥(C ⊓ fixed ρ K) => (z : X)) h
      exact Subtype.ext (Subtype.ext h')
  have hs : A.toRepresentation.IsSemisimpleRepresentation := by
    letI := cd.toNormedAddCommGroup
    letI := InnerProductSpace.ofCore cd.toCore
    exact isSemisimple ha (fun g a b => hi g _ a.2.1 _ b.2.1) ho hc
  exact mem_irrSum hs ha (f := A.toSubmodule.subtype) ⟨fun s => s.2.1, fun _ _ => rfl⟩ ⟨x, hx, hx'⟩

end Abstract

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : DSModel V S}

theorem finRep_mem (g : GfC V) (T : MMap M) (hT : T ∈ allMaps θ M) : finRep M g T ∈ allMaps θ M := by
  have e : finRep M g T = heckeOn M {(g : GA D V)} T := by
    ext v x
    simp [heckeOn, postOn_apply, heckeLin_apply, finRep_apply]
  rw [e]
  exact Submodule.subset_span (GlobalTheory.SphericalOps.isMultMap_single ((GlobalTheory.MultMem.mem_mult_iff ..).1 hT) g.2)

theorem isMultiplicityInner_finRep {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (g : GfC V) {T T' : MMap M} (hT : T ∈ allMaps θ M) (hT' : T' ∈ allMaps θ M)
    {c : ℂ} (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 (finRep M g T) (finRep M g T') c := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  intro v v'
  have := GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (T v x) * T' v' x) g hF fun γ hγ x => by
    rw [(GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T hT v).2 γ hγ, (GlobalTheory.SchurConst.left_cont_of_mem θ M _ _ T' hT' v').2 γ hγ]
  exact ⟨this.1.1 (h v v').1, this.2.trans (h v v').2⟩

theorem finiteDimensional_fixed (hP : GlobalTheory.Published.HarishChandraFinite) (hθ : IsInfFam θ) (K : Subgroup (GfC V))
    (hK : IsOpen (K : Set (GfC V))) : FiniteDimensional ℂ ↥(allMaps θ M ⊓ fixed (finRep M) K) := by
  obtain ⟨N, hN, e⟩ := isOpen_induced_iff.1 hK
  have hmem : ∀ k : GfC V, (k : GA D V) ∈ N ↔ k ∈ K := fun k => Set.ext_iff.1 e k
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N (hN.mem_nhds ((hmem 1).2 K.one_mem))
  haveI := GlobalTheory.MultFinite.hcFinite (M := M) (J := N ∩ GfC V) (χ := fun _ => 1) hP hθ
    ⟨U, hU, fun k hk hf => ⟨⟨hUN k hk hf, hf⟩, rfl⟩⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Mult θ M (N ∩ GfC V) fun _ => 1) fun T hT => Submodule.subset_span ?_
  have h := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨h.aut, h.cusp, fun v k hk g => ?_, h.equiv, h.cont⟩
  have := congrArg (fun T : MMap M => T v g) (mem_fixed.1 hT.2 ⟨k, hk.2⟩ ((hmem ⟨k, hk.2⟩).1 hk.1))
  rw [one_mul]
  exact this

theorem exists_compact_open (V : HSp D) : ∃ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) ∧ IsCompact (K : Set (GfC V)) := by
  obtain ⟨_, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨N, hN, h1⟩ := exists_compact_mem_nhds (1 : GA D V)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V N h1
  refine ⟨U.subgroupOf (GfC V), hU.preimage continuous_subtype_val, ?_⟩
  refine ((GlobalTheory.Ker.CongTop.isClosed_GfC V).isClosedEmbedding_subtypeVal.isCompact_preimage hN).of_isClosed_subset
    ((U.isClosed_of_isOpen hU).preimage continuous_subtype_val) fun k hk => hUN k hk k.2

theorem cuspDecomp : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, CuspDecomp D := by
  intro hP hQ D θ hθ V S M
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hμ : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, hF⟩ := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V _ hμ).2
  have hS : SchurMult θ M ∅ (fun _ => 1) _ 𝓕 := GlobalTheory.MultFinite.schurMult hQ Measure.haar 𝓕
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D θ V S M _ _ _ 𝓕 hθ hμ hF hS (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  obtain ⟨K, ho, hc⟩ := exists_compact_open V
  refine isDecomp_of_form (finRep M) _ finRep_mem (ipM M Measure.haar 𝓕) h1 h2 (fun g T hT T' hT' => ?_)
    (finiteDimensional_fixed hP hθ) ho hc
  have h := isMultiplicityInner_finRep hμ hF g hT hT' (ipM_spec M _ 𝓕 T T' (hS hθ hμ hF T hT T' hT'))
  exact hasPeterssonInner_unique M _ 𝓕 _ _ v hv (ipM_spec M _ 𝓕 _ _ ⟨_, h⟩) h

end GlobalTheory.CuspDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Wsp (lam : InfinitePlace E → DomWeight n) : Type :=
  PiTensorProduct ℂ fun v : InfinitePlace E => nablaSq ℂ n (lam v)

def wAt (lam : InfinitePlace E → DomWeight n) (γ : UE E n) : Wsp lam →ₗ[ℂ] Wsp lam :=
  PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding γ.1)

def vecM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) where
  carrier := {F | (∀ (γ : UE E n) x, F (finPt γ * x) = (wAt lam γ⁻¹).dualMap (F x)) ∧
    ∀ k ∈ globLev S K', ∀ x, F (x * k) = F x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 γ x, hb.1 γ x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 γ x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def hopM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) :
    (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) :=
  levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam))) (globLev S (KL n)) (globLev S K') (globFn S f)
    LinearMap.id

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem trace_piMap {ι : Type} [Fintype ι] {M : ι → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ j, (bc c).repr (f c (bc c j)) j := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (bc c), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Fintype.prod_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem finrank_wsp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (lam : InfinitePlace E → DomWeight n) :
    (Module.finrank ℂ (Wsp lam) : ℂ) = dimW lam := by
  rw [← LinearMap.trace_id, ← PiTensorProduct.map_id, trace_piMap]
  unfold dimW
  simp

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrix
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem val_spMap_pt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (σ : Ω →+* K) (x : Ω) : M.val (spMap σ ≫ M.pt) x = σ x := by
  have hx : x ∈ M.O (genericPoint M.Z) := by rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have := M.val_spMap_comp σ M.pt (M.pt_specializes _ _) ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val, RatModel.val_pt] at this
  exact this

theorem flag_conv : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K) (U : Mat m K), spMap ψ₁ ≫ (ratOf Y).pt ≫ f = spMap ψ₂ ≫ (ratOf Y).pt ≫ f → Bears E' φ A (U * (B * (A.map φ)⁻¹).map ψ₁) (spMap ψ₂ ≫ (ratOf Y).pt) → (∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (U * (B.map ψ₁ * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hR B hB A hA K _ ψ₁ ψ₂ U hpt hBe
  have hom : (ratOf Y).pt ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hR.hom
  have key : ∀ σ : Y.Fn →+* K, spMap σ ≫ (ratOf Y).pt ≫ f = spMap (σ.comp φ.toRingHom) ≫ (ratOf X).pt := by
    intro σ
    rw [hom]
    show Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map (CommRingCat.ofHom (σ.comp φ.toRingHom)) ≫ _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).symm
  have h1 : ∀ u : X.Fn, ψ₁ (φ u) = ψ₂ (φ u) := by
    intro u
    have e1 := val_spMap_pt (ratOf X) (ψ₁.comp φ.toRingHom) u
    have e2 := val_spMap_pt (ratOf X) (ψ₂.comp φ.toRingHom) u
    rw [← key, hpt, key] at e1
    exact e1.symm.trans e2
  refine ⟨h1, ?_⟩
  obtain ⟨A', hA', hP⟩ := hBe
  have hgen : (spMap ψ₂ ≫ (ratOf Y).pt) (IsLocalRing.closedPoint K) = genericPoint Y.X :=
    (ratOf Y).pt_apply _
  rw [hgen] at hA'
  have hval : (ratOf Y).val (spMap ψ₂ ≫ (ratOf Y).pt) = ψ₂ := funext (val_spMap_pt (ratOf Y) ψ₂)
  rw [hval] at hP
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hBd : ∀ τ, (B τ).det ≠ 0 := Fr.det_ne hB
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  set C : Mat m Y.Fn := A.map φ with hC
  have hCd : ∀ τ, (C τ).det ≠ 0 := fun τ => by
    rw [hC]; exact fun h0 => (map_ne_zero φ.toRingHom).2 (hAd τ) ((Mat.det_map A φ.toRingHom τ).symm.trans h0)
  have hCψ : C.map ψ₁ = C.map ψ₂ := by
    funext τ; ext i j; exact h1 (A τ i j)
  have hC2d : ∀ τ, (C.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hCd τ)
  have hA'2d : ∀ τ, (A'.map ψ₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA'd τ)
  have e : U * (B * C⁻¹).map ψ₁ * ((A' * C⁻¹).map ψ₂)⁻¹ = U * B.map ψ₁ * (A'.map ψ₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hCψ, Mat.mul_inv_rev, Mat.inv_inv hC2d]
    rw [mul_assoc U, mul_assoc (B.map ψ₁), ← mul_assoc (C.map ψ₂)⁻¹, Mat.inv_mul hC2d, one_mul, ← mul_assoc]
  rw [e] at hP
  have hQ : Par m (⊤ : Subring K) ((A' * B⁻¹).map ψ₂) := by
    have := (Fr.mem_iff hB).1 hA'
    exact this.map ψ₂ (fun _ _ => trivial)
  have := hP.mul hQ
  rw [Mat.map_mul, Mat.map_inv] at this
  have e2 : U * B.map ψ₁ * (A'.map ψ₂)⁻¹ * (A'.map ψ₂ * (B.map ψ₂)⁻¹) = U * (B.map ψ₁ * (B.map ψ₂)⁻¹) := by
    rw [mul_assoc (U * B.map ψ₁), ← mul_assoc (A'.map ψ₂)⁻¹, Mat.inv_mul hA'2d, one_mul, mul_assoc]
  rwa [e2] at this

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem formalDegreeUpperC_of_hypotheses : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  intro hp D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  obtain ⟨hcore, -, hσ, -⟩ := hL
  have h5 : GlobalTheory.Core5 R F := ⟨hcore.lev, hcore.grp, hcore.fam, hcore.models, hcore.thP⟩
  intro Fr hFr ρ mR hmR e he
  dsimp only
  obtain ⟨hanti, hhalf, hwid⟩ := _root_.GlobalTheory.LowRow.lam_par_width R F h5 i σ s hσ ρ
  have hsig : ∀ ρ', ((Wc D i).sig (tauE D ρ')).1 + ((Wc D i).sig (tauE D ρ')).2 = (Wc D i).rank :=
    fun ρ' => (_root_.GlobalTheory.LowRow.lift_rows_antitone D i σ ρ').2.2.1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have h1 : 1 ≤ (Wc D i).rank := by
    rw [hrk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]; omega
  have h3 : 3 ≤ D.R.nV := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m; have := D.R.three_m_lt_t
    simp only [Formalism.BasicNotions.Ranks.nV, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨hint, hinv⟩ := _root_.GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq hp D.cd (Wc D i) _ (R.MW i σ) Fr hFr hsig ρ hanti hhalf _ he
  have hm := _root_.GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd D.cd _ _ mR hmR
  rw [hsig ρ] at hm
  obtain ⟨hvol, hQpos, hlog⟩ := _root_.GlobalTheory.LowRow.formalDeg_div_volU_log_bound (Wc D i).rank D.R.nV (degAt D i σ ρ) ((R.MW i σ).lam ρ) h1 h3
    (by positivity) hanti hwid
  have e1 : (((Wc D i).rank : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  rw [e1] at hlog
  subst hm
  refine ⟨hint.smul_measure ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul]
    refine mul_pos hvol ?_
    have : 0 < (∫ b : Upq (Wc D i) ρ, ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(D.cd.cd _ _))⁻¹ := by
      rw [hinv]; exact hQpos
    exact inv_pos.mp this
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul, mul_inv, hinv, mul_comm, ← div_eq_mul_inv]
    exact hlog

end GlobalTheory.LowRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.FSDet

theorem sum_conj_mul_self {n : ℕ} (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (∑ j, starRingEnd ℂ (v j) * v j) = (‖v‖ : ℂ) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq v
  have h2 : ((‖v‖ : ℂ)) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, h]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem det_one_add_vecMulVec' {m : Type} [Fintype m] [DecidableEq m] (a b : m → ℂ) :
    (1 + Matrix.vecMulVec a b).det = 1 + a ⬝ᵥ b := by
  have := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  rw [Matrix.vecMulVec_eq (ι := Unit), this, dotProduct_comm]

end GlobalTheory.FSDet

namespace GlobalTheory.FSDet

theorem det_fubiniStudy_hess :
    ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  intro n v
  rw [_root_.GlobalTheory.FubiniStudyHessian.cHess_log_one_add_normSq n v]
  set t : ℂ := 1 + (‖v‖ : ℂ) ^ 2 with ht
  have htr : t = ((1 + ‖v‖ ^ 2 : ℝ) : ℂ) := by rw [ht]; push_cast; rfl
  have ht0 : t ≠ 0 := by
    rw [htr]; exact_mod_cast (by positivity : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0)
  have hM : (Matrix.of (fun j l => (if j = l then (1:ℂ) else 0) / t - (starRingEnd ℂ (v j) * v l) / t ^ 2) : Matrix (Fin n) (Fin n) ℂ)
      = t⁻¹ • (1 + Matrix.vecMulVec (fun j => -(starRingEnd ℂ (v j)) / t) (fun l => v l)) := by
    ext j l
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
    ring
  rw [hM, Matrix.det_smul, det_one_add_vecMulVec', Fintype.card_fin]
  have hdot : (fun j => -(starRingEnd ℂ (v j)) / t) ⬝ᵥ (fun l => v l) = -((‖v‖ : ℂ) ^ 2) / t := by
    rw [← sum_conj_mul_self v, dotProduct, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : t⁻¹ ^ n * (1 + -((‖v‖ : ℂ) ^ 2) / t) = (((1 + ‖v‖ ^ 2 : ℝ) ^ (n + 1))⁻¹ : ℝ) := by
    have h1 : (1 + -((‖v‖ : ℂ) ^ 2) / t) = t⁻¹ := by
      field_simp
      rw [ht]; ring
    rw [h1, ← pow_succ, inv_pow, htr]
    push_cast
    rfl
  rw [hdot, hval, Complex.ofReal_re]

end GlobalTheory.FSDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImageProperties
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem goodPatch_image : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  intro F _ σ X m E O H e S A W c h
  refine ⟨e.isOpen_image_of_subset_source h.isOpen h.sub, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨z, ⟨hO, hW⟩, rfl⟩
      exact ⟨⟨z, hW, rfl⟩, (h.mem z hW).1 hO⟩
    · rintro ⟨⟨z, hW, rfl⟩, hv⟩
      exact ⟨z, ⟨(h.mem z hW).2 hv, hW⟩, rfl⟩
  · intro K hK hKW
    haveI : CompactSpace (CxPts X.str σ) := CxPts.compactSpace σ X.isProjOver
    exact hK.isCompact.image_of_continuousOn (e.continuousOn.mono (hKW.trans h.sub))

end GlobalTheory.GoodTop
end

