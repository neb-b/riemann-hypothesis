module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImage
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLiftTwistedModelIffUntwisted
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open Formalism.L2.Col
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.HeckeLifts₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

abbrev SysL (A3 : FamIn3 K G Pl0 I0 Ty T m) (j : Fin m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

end Abstract

section TwEig

variable {s : Bool} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tw_map_mul (a b : Module.End ℂ E) : (Tw.map s (a * b) : Module.End ℂ (Tw s E)) = Tw.map s a * Tw.map s b :=
  LinearMap.ext fun _ => rfl

theorem tw_map_pow (a : Module.End ℂ E) (k : ℕ) : (Tw.map s (a ^ k) : Module.End ℂ (Tw s E)) = Tw.map s a ^ k := by
  induction k with
  | zero => exact LinearMap.ext fun _ => rfl
  | succ k ih => rw [pow_succ, tw_map_mul, ih, pow_succ]

theorem tw_map_sub_smul (a : Module.End ℂ E) (μ : ℂ) :
    (Tw.map s a - μ • 1 : Module.End ℂ (Tw s E)) = Tw.map s (a - cj s μ • 1) :=
  LinearMap.ext fun _ => rfl

theorem mem_maxGen_tw (a : Module.End ℂ E) (μ : ℂ) (v : Tw s E) :
    v ∈ Module.End.maxGenEigenspace (Tw.map s a : Module.End ℂ (Tw s E)) μ ↔ Tw.out v ∈ a.maxGenEigenspace (cj s μ) := by
  simp only [Module.End.mem_maxGenEigenspace]
  rw [tw_map_sub_smul]
  refine exists_congr fun k => ?_
  rw [← tw_map_pow]
  exact Iff.rfl

theorem eigAt_tw {I : Type} (h : I → Module.End ℂ E) (y : I → ℂ) :
    eigAt (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) y = Tw.sub s (eigAt h fun i => cj s (y i)) := by
  refine SetLike.ext fun v => ?_
  rw [show v ∈ Tw.sub s (eigAt h fun i => cj s (y i)) ↔ Tw.out v ∈ eigAt h (fun i => cj s (y i)) from Iff.rfl]
  simp only [eigAt, Submodule.mem_iInf]
  exact forall_congr' fun i => mem_maxGen_tw (h i) (y i) v

theorem sub_iSup {ι : Type} (V : ι → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun c v hv => (le_iSup V c) hv)
  exact Submodule.iSup_induction V (motive := fun y => (Tw.mk s y : Tw s E) ∈ ⨆ c, Tw.sub s (V c)) hx
    (fun c y hy => Submodule.mem_iSup_of_mem c hy) (zero_mem _) (fun a b ha hb => add_mem ha hb)

theorem sub_iSup_prop {P : Prop} (V : P → Submodule ℂ E) : Tw.sub s (⨆ c, V c) = ⨆ c, Tw.sub s (V c) := by
  by_cases hP : P
  · rw [iSup_pos hP, iSup_pos hP]
  · rw [iSup_neg hP, iSup_neg hP]
    rfl

theorem eigSum_tw {I : Type} (h : I → Module.End ℂ E) (Q : (I → ℂ) → Prop) :
    eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (eigSum h fun x => Q fun i => cj s (x i)) := by
  unfold eigSum
  rw [sub_iSup]
  simp only [sub_iSup_prop, eigAt_tw]
  have hcc : ∀ y : I → ℂ, (fun i => cj s (cj s (y i))) = y := fun y => funext fun i => cj_cj s (y i)
  refine le_antisymm (iSup₂_le fun y hy => le_iSup₂_of_le (fun i => cj s (y i)) (by rw [hcc]; exact hy) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (fun i => cj s (x i)) hx ?_)
  rw [hcc]

end TwEig

section Concrete

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def twE (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Module.End ℂ ((R.toCx3 F).W j) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H : Module.End ℂ (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H))

theorem theta_jL (j : Fin D.R.m) (t : T) (y : (A3.A.fam.L j t).S.Forms) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t y) =
      (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (R.jV j t y)) :
        Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) := rfl

theorem twE_smul (j : Fin D.R.m) (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H) (c : ℂ) (v : (R.HW j (sg0 D A3.A)).H) :
    twE R F j H (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) v : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) =
      (c • Tw.mk (twAt D.what₂.embLL A3.A.v0) (H v) : Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) :=
  (Tw.map (twAt D.what₂.embLL A3.A.v0) H).map_smul c _

theorem intw_of_rat (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)))
    (u : (R.toCx3 F).FLC j t) :
    (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have key : ((R.toCx3 F).θ' j t) ∘ₗ ((R.toCx3 F).opLC j t (Sum.inl i)) = (twE R F j H) ∘ₗ ((R.toCx3 F).θ' j t) := by
    refine LinearMap.ext_on (hK j t).2 ?_
    rintro _ ⟨k, rfl⟩
    have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) (CxData.bL (A := A3.fam3.amb3) j t k)
    simp only [LinearMap.comp_apply]
    refine (congrArg ((R.toCx3 F).θ' j t) e1.symm).trans ?_
    refine (theta_jL j t _).trans ?_
    refine Eq.trans ?_ (congrArg (twE R F j H) (theta_jL j t _).symm)
    refine Eq.trans ?_ (twE_smul j H _ _).symm
    exact congrArg (fun v => (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) v :
      Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H)) (h _)
  exact LinearMap.congr_fun key u


abbrev SysC (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) :
    ((A3.liftI j A3.A.fam.μ0).OpIx → ℂ) → Prop :=
  cxSys D.what₂.embLL ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1))

theorem sysL_cj (R : RealDat3 D A3 Ks) (j : Fin D.R.m) (p : A3.fam3.base3.Ix) (x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) :
    SysL A3 j p (fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) ↔ SysC A3 j p x := by
  constructor
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i) := congrFun hy.2 i
    rw [R.toRealDat.emb0] at e
    rw [← cj_cj (twAt D.what₂.embLL A3.A.v0) (x i), e, cj_cj]
  · refine fun h => Exists.elim h fun y hy => ⟨y, hy.1, funext fun i => ?_⟩
    have e : x i = D.what₂.embLL (y i) := congrFun hy.2 i
    show cj (twAt D.what₂.embLL A3.A.v0) (x i) = A3.A.v0.embedding (y i)
    rw [R.toRealDat.emb0, e]

def unE (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : Module.End ℂ (Tw s E)) : Module.End ℂ E where
  toFun v := Tw.out (h (Tw.mk s v))
  map_add' x y := (congrArg Tw.out (h.map_add (Tw.mk s x) (Tw.mk s y)))
  map_smul' c v := by
    have e : (Tw.mk s (c • v) : Tw s E) = cj s c • Tw.mk s v := by
      show c • v = cj s (cj s c) • v
      rw [cj_cj]
    show Tw.out (h (Tw.mk s (c • v))) = c • Tw.out (h (Tw.mk s v))
    rw [e, map_smul, Tw.out_smul, cj_cj]

theorem twE_commute (j : Fin D.R.m) (a b : Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    Commute (twE R F j a) (twE R F j b) ↔ Commute a b :=
  ⟨fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v, fun h => LinearMap.ext fun v => LinearMap.congr_fun h.eq v⟩

theorem rat_of_intw (hM : R.toRealDat.IsModels) (j : Fin D.R.m) (hph : R.phs j ≠ 0) (t : T) (i : (A3.liftI j t).OpIx)
    (H : Module.End ℂ (R.HW j (sg0 D A3.A)).H)
    (h : ∀ u, (R.toCx3 F).θ' j t ((R.toCx3 F).opLC j t (Sum.inl i) u) = twE R F j H ((R.toCx3 F).θ' j t u))
    (f : (A3.A.fam.L j t).S.Forms) :
    R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = H (R.thG j t (R.jV j t f)) := by
  have hK := RealDat3.kFormL_of (F := F) hM
  have e1 := CxData.jL_opL (R.toCx3 F) hK j t (Sum.inl i) f
  have e2 := (congrArg ((R.toCx3 F).θ' j t) e1).trans (h _)
  have e3 := ((theta_jL (R := R) (F := F) j t _).symm.trans e2).trans
    ((congrArg (twE R F j H) (theta_jL j t f)).trans (twE_smul j H _ _))
  exact smul_right_injective (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j (sg0 D A3.A)).H) hph e3

structure UntwL (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) : Prop where
  rat : ∀ j t i f, R.thG j t (R.jV j t ((A3.liftI j t).opAll i f)) = g j t i (R.thG j t (R.jV j t f))
  comm : ∀ j, PairComm (g j A3.A.fam.μ0)
  parts : ∀ j p, R.Wp3 j p = eigSum (g j A3.A.fam.μ0) (SysC A3 j p)

theorem sub_inj (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A B : Submodule ℂ E}
    (h : Tw.sub s A = Tw.sub s B) : A = B :=
  SetLike.ext fun x => SetLike.ext_iff.1 h (Tw.mk s x)

theorem hecke_theta_lift_twisted_model_iff_untwisted (hM : R.toRealDat.IsModels) (hph : ∀ j, R.phs j ≠ 0)
    (g : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (R.HW j (sg0 D A3.A)).H) :
    HeckeIntertwiningLifts A3 (R.toCx3 F) (fun j t i => twE R F j (g j t i)) ↔ UntwL (R := R) g := by
  have hp : ∀ j p, eigSum (fun i => twE R F j (g j A3.A.fam.μ0 i)) (SysL A3 j p) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0) (eigSum (g j A3.A.fam.μ0) (SysC A3 j p)) := fun j p => by
    have e := eigSum_tw (s := twAt D.what₂.embLL A3.A.v0) (g j A3.A.fam.μ0) (SysL A3 j p)
    have e' : (fun x : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ => SysL A3 j p fun i => cj (twAt D.what₂.embLL A3.A.v0) (x i)) =
        SysC A3 j p := funext fun x => propext (sysL_cj R j p x)
    rw [e'] at e
    exact e
  constructor
  · intro h
    refine ⟨fun j t i f => rat_of_intw hM j (hph j) t i _ (h.intw j t i) f, fun j i i' => (twE_commute j _ _).1 (h.comm j i i'), fun j p => ?_⟩
    refine sub_inj (twAt D.what₂.embLL A3.A.v0) ?_
    exact (h.parts j p).trans (hp j p)
  · intro h
    refine ⟨fun j t i u => intw_of_rat hM j t i _ (h.rat j t i) u, fun j i i' => (twE_commute j _ _).2 (h.comm j i i'), fun j p => ?_⟩
    refine Eq.trans ?_ (hp j p).symm
    exact congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (h.parts j p)

theorem phs_ne_zero (hC : R.WeakCharacterisation F) (j : Fin D.R.m) : R.phs j ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [(hC.phase j).1]; exact one_ne_zero)

def unW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (h : Module.End ℂ ((R.toCx3 F).W j)) :
    Module.End ℂ (R.HW j (sg0 D A3.A)).H :=
  unE (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) h

theorem untw_of_hH (hC : R.WeakCharacterisation F) {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ ((R.toCx3 F).W j)}
    (hH : HeckeIntertwiningLifts A3 (R.toCx3 F) hW) : UntwL (R := R) fun j t i => unW R F j (hW j t i) :=
  (hecke_theta_lift_twisted_model_iff_untwisted (F := F) hC.base.models (phs_ne_zero hC) fun j t i => unW R F j (hW j t i)).1 hH

end Concrete

end GlobalTheory.HeckeLifts₂

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlace
section
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

theorem latAt_lattice {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    ∃ g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v), IsUnit g.det ∧
      X.latAt v j L = colSpan (X.G.P.W v) g ∧ len X v j L = -ordP (X.G.P.W v) p g.det := by
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  cases j with
  | zero =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v 0 L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v 0 L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg
  | succ j =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v (j + 1) L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v (j + 1) L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg

theorem Pj_m_succ {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) : (X.Pj j).m + 1 = NN X.G.P.m X.t j := by
  cases j with
  | zero => simp [NN, Sys.Pj, Fills.Pj]
  | succ j =>
    simp only [NN, Sys.Pj, Fills.Pj, Places.withWt, Sys.t]
    ring

theorem homLat_conj {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (M g : Matrix (Fin k) (Fin k) Qq) (M' g' : Matrix (Fin k') (Fin k') Qq) (hM' : IsUnit M'.det)
    (z : Matrix (Fin k') (Fin k) Qq) :
    z ∈ homLat W (colSpan W (M * g)) (colSpan W (M' * g')) ↔
      ∀ y ∈ colSpan W g, (M'⁻¹ * z * M) *ᵥ y ∈ colSpan W g' := by
  rw [← colSpan_mul, ← colSpan_mul, mem_homLat]
  have hinv : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hM'
  have hinv' : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hM'
  constructor
  · intro h y hy
    obtain ⟨u, hu, hu'⟩ := h (M *ᵥ y) (Submodule.mem_map_of_mem hy)
    have e : (M'⁻¹ * z * M) *ᵥ y = u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : z *ᵥ (M *ᵥ y) = M' *ᵥ u := hu'.symm
      rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact hu
  · rintro h _ ⟨y, hy, rfl⟩
    have e : z *ᵥ ((M.mulVecLin.restrictScalars W) y) = M' *ᵥ ((M'⁻¹ * z * M) *ᵥ y) := by
      change z *ᵥ (M *ᵥ y) = _
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv', Matrix.one_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (h y hy)

theorem vol_main : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  intro D p _ X v j ρ P hA h1 h2
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  obtain ⟨φ, hφ, hop, hnb⟩ := _root_.GlobalTheory.DenseCompl.completion_ringEquiv_of_dense P p hS.p_unif hS.eq_sum_herm_smul_frame_of_inW ρ h1 h2
  refine ⟨φ, hφ, ?_⟩
  intro M M' hM hM' N N' S hSq
  have key : ∀ q ∈ S, ∃ (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
      (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      IsUnit (M * g).det ∧ IsUnit (M' * g').det ∧
      (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      (∀ z, X.ind v j q.1 q.2 (M'⁻¹ * z * M) = 1 ↔ z ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      ordP (X.G.P.W v) p (M * g).det = ordP (X.G.P.W v) p M.det - len X v j q.1 ∧
      ordP (X.G.P.W v) p (M' * g').det = ordP (X.G.P.W v) p M'.det - len X v (j + 1) q.2 := by
    intro q hq
    obtain ⟨hL, hL', hAdm, hsp, hsp'⟩ := hSq q hq
    obtain ⟨g, hg, hgL, hlen⟩ := latAt_lattice X v j q.1 hL
    obtain ⟨g', hg', hgL', hlen'⟩ := latAt_lattice X v (j + 1) q.2 hL'
    have hMg : IsUnit (M * g).det := by rw [Matrix.det_mul]; exact hM.mul hg
    have hMg' : IsUnit (M' * g').det := by rw [Matrix.det_mul]; exact hM'.mul hg'
    have hNa : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M * g) := by rw [hsp, hgL, colSpan_mul]
    have hNb : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M' * g') := by rw [hsp', hgL', colSpan_mul]
    obtain ⟨-, -, ⟨hFG, hspan, -⟩, ⟨hFG', hspan', -⟩⟩ := hAdm
    refine ⟨g, g', hMg, hMg', fun y => ?_, fun z => ?_, ?_, ?_⟩
    · exact _root_.GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat P p hS.p_unif ρ h2 φ hφ hop hnb (TaylorLogMetric.YYl D (N q.1) (N' q.2)) _ _ hMg hMg'
        (_root_.GlobalTheory.TwU.map_mem_homLat_of_mem_YYl D P p hS.p_unif ρ hA h1 _ _ _ _ hNa hNb)
        (_root_.GlobalTheory.VolOnto.homLat_le_span_YYl D P p hS.p_unif ρ hA h1 _ _ hFG hFG' hspan hspan' _ _ hMg hMg' hNa hNb) y
    · rw [homLat_conj M g M' g' hM' z, ← hgL, ← hgL']
      unfold Sys.ind
      split_ifs with h
      · exact iff_of_true rfl h
      · exact iff_of_false (by norm_num) h
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM.ne_zero hg.ne_zero, hlen]
      ring
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM'.ne_zero hg'.ne_zero, hlen']
      ring
  intro q hq
  obtain ⟨g, g', hMg, hMg', hY, hind, ho, ho'⟩ := key q hq
  refine ⟨fun y => (hY y).trans (hind _).symm, fun q₀ hq₀ => ?_⟩
  obtain ⟨g₀, g₀', hMg₀, hMg₀', hY₀, -, ho₀, ho₀'⟩ := key q₀ hq₀
  let e : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) →+
      Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
    φ.toAddEquiv.toAddMonoidHom.mapMatrix
  have he : Function.Surjective e := fun z => ⟨z.map φ.symm, by ext i l; simp [e]⟩
  have hYc : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q.1) (N' q.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hYc₀ : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q₀.1) (N' q₀.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q₀.1) (N' q₀.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hrel : ∀ A B : AddSubgroup (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      ((A.comap e).addSubgroupOf (B.comap e)).index = A.relIndex B := fun A B => by
    change (A.comap e).relIndex (B.comap e) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective he]
  unfold GL3Theta.volP
  rw [hYc _ hY, hYc₀ _ hY₀, hrel, hrel,
    _root_.GlobalTheory.HomLatIndex.relIndex_homLat_ratio p (X.G.P.n' v) hS.p_unif hS.res_card _ _ _ _ hMg₀ hMg hMg₀' hMg', ho, ho', ho₀, ho₀']
  congr 1
  unfold volE
  rw [← Pj_m_succ X j, ← Pj_m_succ X (j + 1)]
  push_cast
  ring

end GlobalTheory.VolAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LabChar

theorem conjPl_eq_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : conjPl P = GlobalTheory.IdemSupport.cP P := by
  apply HeightOneSpectrum.ext
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal.comap (GlobalTheory.IdemSupport.cO D).toRingHom
  have h : Formalism.DivisionValues.cO D.host.E = GlobalTheory.IdemSupport.cO D := rfl
  rw [h]
  have inv : ∀ y, GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) = y := fun y => by
    apply RingOfIntegers.ext
    simp [GlobalTheory.IdemSupport.cO]
  ext x
  rw [Ideal.mem_map_of_equiv, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D y) ∈ P.asIdeal
    rwa [inv]
  · intro hx
    exact ⟨_, hx, inv x⟩

theorem eq_of_fixed {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (hc : conjPl P = P) : f = e := by
  rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
  · exfalso
    have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hcc : Formalism.IndefR.Lev.IsConjPl P P := by
      rw [GlobalTheory.IdemSupport.isConjPl_iff, ← conjPl_eq_cP, hc]
    have hs' := H.2.2.2 P P e hs hcc
    have h' : IsPrimeIdem P (cA D e) (cA D e + cA D (cA D e)) := Or.inl ⟨hs', rfl⟩
    have hee := ((H.2.2.1 P e _ h).2.2.2.1 _ _ h').1
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have e0 : e = 0 := by
      rw [hee, h1] at h2
      exact h2
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (ht x hx0).1 hx
    apply this
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · rfl

theorem fixed_of_tie {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e e) : conjPl P = P := by
  rcases h with ⟨hs, he⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exfalso
    obtain ⟨⟨h1, h2, -⟩, ht⟩ := hs
    have hc : cA D e = 0 := by
      have := he
      nth_rewrite 1 [← add_zero e] at this
      exact (add_left_cancel this).symm
    have e0 : e = 0 := by
      have := congrArg (cA D) hc
      rwa [cA_cA, map_zero] at this
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    apply (ht x hx0).1 hx
    rw [e0, zero_mul, map_zero]
    exact zero_mem _
  · have ht' := GlobalTheory.IdemSupport.Comparison₂.conj ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at ht'
    rw [conjPl_eq_cP]
    apply HeightOneSpectrum.ext
    ext x
    by_cases hx : x = 0
    · subst hx; simp only [zero_mem]
    · rw [ht' x hx, ht x hx]

theorem lab_char (hU : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d') (hS : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g) (hI : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g) : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) := by
  intro D V P d
  have H := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  constructor
  · rintro ⟨R, e, f, ϖ, α, -, h, h1, h2, hd, -, -, hα, hD, -, -⟩
    refine ⟨hD.1, hd, fun hc => ?_⟩
    obtain rfl := eq_of_fixed V h hc
    have he : f * f = f := (H.2.2.1 P f f h).1
    obtain ⟨⟨a, b, ha, -, hb, -, hinv⟩, -⟩ :=
      GlobalTheory.InertDoubleCoset.inert_double_cosets V P f h (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα
    have hϖ0 := GlobalTheory.SphLabelOps.unif_ne_zero h2
    have hx := GlobalTheory.DivDual.divAt_inv_and_mul V f (ϖ : D.host.E) d α he hϖ0 hD
    have h3 := hx.2 a ha b hb
    rw [← hinv] at h3
    exact hU V P f f ϖ (dualLab d) d α⁻¹ h h1 h2 (GlobalTheory.SphLabelOps.dualLab_pairwise hd) hd hx.1 h3
  · rintro ⟨hl, hd, hs⟩
    obtain ⟨e, f, h⟩ := H.2.1 P
    obtain ⟨x, y, hy, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
    by_cases hc : conjPl P = P
    · obtain rfl := eq_of_fixed V h hc
      obtain ⟨g, hg, hD⟩ := hI V P f x y d h hy h1 h2 hl (hs hc)
      exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
    · rcases id h with ⟨hi, rfl⟩ | ⟨rfl, -⟩
      · obtain ⟨g, hg, hD⟩ := hS V P e y d hi h1 h2 hl
        exact GlobalTheory.SphLabelOps.isLab_of_divAt h h1 h2 hd hg hD
      · exact absurd (fixed_of_tie h) hc

theorem labels_char : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) :=
  lab_char _root_.GlobalTheory.DivUnique.div_unique _root_.GlobalTheory.SplitExist.split_exist _root_.GlobalTheory.InertExist.exists_suppF_divAt

end GlobalTheory.LabChar
end

