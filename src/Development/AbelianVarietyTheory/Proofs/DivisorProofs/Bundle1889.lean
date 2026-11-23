module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanks
section
noncomputable section

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem finrank_iSup_of_indep {R V ι : Type} [Field R] [AddCommGroup V] [Module R V] [FiniteDimensional R V]
    [Fintype ι] (S : ι → Submodule R V) (hS : iSupIndep S) :
    finrank R (⨆ i, S i : Submodule R V) = ∑ i, finrank R (S i) := by
  classical
  have key : ∀ s : Finset ι, finrank R (⨆ i ∈ s, S i : Submodule R V) = ∑ i ∈ s, finrank R (S i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
      have hd : Disjoint (S a) (⨆ i ∈ s, S i) := hS.disjoint_biSup (y := (s : Set ι)) (by exact_mod_cast ha)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (S a) (⨆ i ∈ s, S i)
      rw [hd.eq_bot, finrank_bot, add_zero] at h
      exact h
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), S i) = ⨆ i, S i := iSup_congr fun i => iSup_pos (Finset.mem_univ i)
  rw [← hu]
  exact key Finset.univ

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

theorem rankOn_eq_finrank_span (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (Z : Comp Xo c) (G : WTZ D.host.E) :
    rankOn U Z G = finrank c.F (Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G))) := by
  have hset : (partLat U Z G : Set (cuspW Xo c U G)) =
      Submodule.inclusion (cuspOn_le U Z G) '' (latOn U Z G : Set (cuspOn U Z G)) := by
    simp [partLat]
  rw [hset, Submodule.span_image]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (Submodule.inclusion_injective (cuspOn_le U Z G)) _))

end GlobalTheory.RankAdd

namespace GlobalTheory.RankAdd

open NumberField IsDedekindDomain MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

theorem cuspOn_comap_indep {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ D.host.E) :
    iSupIndep (fun Z : Comp Xo c => (cuspOn U Z G).comap (cuspW Xo c U G).subtype) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), (cuspOn U j G).comap (cuspW Xo c U G).subtype) ≤
      LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact GlobalTheory.CuspSplit.idem_mul_eq_zero (Ne.symm hj) (Submodule.mem_comap.1 hy)
  have h0 := hle hx'
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply] at h0
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x :=
        (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (Submodule.mem_comap.1 hx)).symm
    _ = 0 := h0


set_option maxHeartbeats 1000000 in
theorem rankW_eq_finsum_rankOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
    (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  intro D H Dw l Xo c r U x V dict G hU hG
  obtain ⟨-, -, -, hsup⟩ := GlobalTheory.CuspSplit.splits D H Dw l Xo c r U V dict hU G
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)

  obtain ⟨-, ⟨s, hs⟩, htop⟩ := hG
  haveI : FiniteDimensional c.F (cuspW Xo c U G) := by
    refine Module.Finite.of_fg_top ⟨s, ?_⟩
    rw [← htop, ← hs, Submodule.span_span_of_tower]
  set S : Comp Xo c → Submodule c.F (cuspW Xo c U G) :=
    fun Z => Submodule.span c.F (partLat U Z G : Set (cuspW Xo c U G)) with hSdef
  have hspan : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⨆ Z, S Z := by
    apply le_antisymm
    · rw [Submodule.span_le, ← hsup]
      intro y hy
      have hle : (⨆ Z : Comp Xo c, partLat U Z G) ≤ (⨆ Z, S Z).restrictScalars (𝓞 c.F) :=
        iSup_le fun Z z hz => (le_iSup S Z) (Submodule.subset_span hz)
      exact hle hy
    · exact iSup_le fun Z => Submodule.span_mono (by rw [← hsup]; exact le_iSup (fun Z => partLat U Z G) Z)
  have hind : iSupIndep S := (cuspOn_comap_indep U G).mono fun Z =>
    Submodule.span_le.2 fun y hy => Submodule.mem_comap.2 (GlobalTheory.CuspSplit.coe_mem_of_mem_partLat hy)
  rw [finsum_eq_sum_of_fintype]
  show finrank c.F (Submodule.span c.F (latW U G : Set (cuspW Xo c U G))) = _
  rw [hspan, finrank_iSup_of_indep S hind]
  exact Finset.sum_congr rfl fun Z _ => (rankOn_eq_finrank_span U Z G).symm

end GlobalTheory.RankAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev ThAt (a : AE D) (b Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) a
    (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 b Φ f


open Classical in
def adjDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0


variable {R} in
open Classical in
def keepPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∈ Q'


variable {R} in
open Classical in
def flipPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∉ Q'

end Defs

theorem suppAt_mul' {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hm : mt V (a * b) = mt V a * mt V b := by first | rfl | simp [Formalism.L2.Theta.mt]
  have key : mt V a * mt V b - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by noncomm_ring
  rw [hm, key, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

end GlobalTheory.BigOn.Exp.TupLe.Swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SympInv
open Matrix
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_eq_trace (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB x y = trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ i : α, ∑ k : α, ∑ l : β, x i j * JA i k * JB j l * c (y k l) =
      ∑ l : β, ∑ k : α, x i j * JA i k * c (y k l) * JB j l := fun i => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm

theorem hTens_act (JA : Matrix α α E) (JB : Matrix β β E) (G : Matrix α α E) (H : Matrix β β E)
    (hG : Gᵀ * JA * G.map c = JA) (hH : Hᵀ * JB * H.map c = JB) (x y : Matrix α β E) :
    GlobalTheory.WeilM.hTens c JA JB (G * x * Hᵀ) (G * y * Hᵀ) = GlobalTheory.WeilM.hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (G * y * Hᵀ).map c = G.map c * y.map c * (H.map c)ᵀ := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  have e2 : (H.map c)ᵀ * JBᵀ * H = JBᵀ := by
    conv_rhs => rw [← hH]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [show H * (xᵀ * Gᵀ) * JA * (G.map c * y.map c * (H.map c)ᵀ) * JBᵀ =
      H * (xᵀ * (Gᵀ * JA * G.map c) * y.map c * ((H.map c)ᵀ * JBᵀ)) by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, hG, Matrix.mul_assoc _ _ H, e2]

end GlobalTheory.SympInv

namespace GlobalTheory.SympInv

theorem symp_act : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (g : UA σ X.J) (h : UA σ W.J) (x u : Matrix (Fin n) (Fin d) (AE F E)),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u := by
  intro F E _ _ _ _ _ σ n d X W g h x u
  have hg : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
  have hh : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
  unfold GlobalTheory.WeilM.symp
  rw [hTens_act (cA σ) (incM F X.J) (incM F W.J) (mat g) (mat h) hg hh x u]

end GlobalTheory.SympInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTypeVec

theorem typeVec_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  obtain ⟨t, hQt⟩ := hQt
  have sdV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hvac := hK.vecOf.1
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  have hth0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hvac.2.theta
  have hlat := hvac.2.lat
  have fixQ := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac R.ψ hlat heQ
  have hQpl := hK.pl
  have hdisj : Disjoint R.Pg (R.Q t) := Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hC.lev t
  obtain ⟨⟨esg, hesg, hegs⟩, -⟩ := heg
  obtain ⟨⟨esQ, hesQ, heQs⟩, -⟩ := heQ
  have h1 : eQ * eg = 0 := by
    rw [hegs, heQs, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    exact Formalism.IndefR.Fin.idem_orth ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP)
      (fun h => Finset.disjoint_left.1 hdisj hP (h ▸ hQt hP'))
  have h2 : eQ * cA D eg = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hegs, heQs, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    refine Formalism.IndefR.Fin.idem_orth_conj ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP) fun hc => ?_
    obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hQpl P' hP'
    obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
    exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top hq (D.host.g_prime k) (hqg k)
      (Formalism.IndefR.Fin.nat_mem_of_conj hc (Formalism.IndefR.Fin.char_mem hq hcard))
      (Formalism.IndefR.Fin.g_mem_of_div R.toLevCh.C hk)
  have h3 : eg * cA D eQ = 0 := by
    have := congrArg (cA D) h2
    rwa [map_mul, Formalism.L2.Theta.cA_cA, map_zero, mul_comm] at this
  have h4 : cA D eg * cA D eQ = 0 := by rw [← map_mul, mul_comm, h1, map_zero]
  refine ⟨sdV, sdW, GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hvac.2.inf hfg hth0, fun u hu hh => ?_⟩
  refine GlobalTheory.VacFix.heisO_fix_of_isThetaAt D R.ψ _ _ (cA D eg) _ 1 (R.vacP i) _ fg u hfg
    (fun a b => ?_) (fun a b => ?_) (fixQ u hu hh)
  · rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm (cA D eg), h2, zero_mul]
    · rw [← hh a b, ← mul_assoc, h4, zero_mul]
  · rw [Formalism.L2.Theta.cA_cA]
    rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm eg, h1, zero_mul]
    · rw [← hh a b, ← mul_assoc, h3, zero_mul]

end GlobalTheory.KerTypeVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

section IntWeight

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_borR_of_borChart_int [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

open Formalism.L2.Pj AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem evR_frBor_of_mem_secZ (hS : Out.SecBaseChangeSt) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (hb : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  have hB := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1
  have hall := _root_.GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact evalAt_borR_of_borChart_int hB e hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

theorem test_value_eq_const_mul_reading_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (p : TRing c.F)
    (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) :
    ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ secZ Xo c e,
      Formalism.L2.Pj.toC (ψ (f p y)) = u * rdU U f k x.1 := by
  obtain ⟨-, -, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 z
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨k, x, Formalism.L2.Pj.toC ((∏ i, t i ^ e i : (CAt σ)ˣ) : CAt σ), fun f hf => ?_⟩
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
  have hev : evR Xo c f z = ψ (f p y) := by
    unfold evR evalAt
    rw [dite_eq_left hft]
    exact hW f hf.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  have hw := evR_frBor_of_mem_secZ hS Xo c e hf (CAt σ) t _ _ ht
  rw [← hev, hw]
  classical
  show _ = _ * (if h : x.1 ∈ (U.X k).dom then Formalism.L2.Pj.toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0)
  rw [dite_eq_left x.2]
  rfl

theorem reading_linearIndependent_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (m : ℕ) (b : Fin m → Rul Xo c)
    (hb : ∀ i, b i ∈ secZ Xo c e) (hli : LinearIndependent c.F b) :
    LinearIndependent ℂ (fun i => rdU U (b i)) := by
  have h := fun p y ψ => test_value_eq_const_mul_reading_secZ hS U hU e p y ψ
  have : CharZero c.F := RingHom.charZero σ
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
    intro θ
    have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
      funext p y
      have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
        obtain ⟨k', x, u, hk⟩ := h p y ψ
        have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
          intro i; rw [show cvalR σ (ψ (b i p y)) = Formalism.L2.Pj.toC (ψ (b i p y)) from rfl, hk (b i) (hb i)]; ring
        have e2 := congrFun (congrFun hw k') x.1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
        simp_rw [e1]
        rw [← Finset.mul_sum, e2, mul_zero]) θ
      simpa [Finset.sum_apply] using hpt
    exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
  intro i
  exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i

theorem cuspW_finiteDimensional_of_isUnf (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (G : WTZ E) :
    FiniteDimensional c.F (cuspW Xo c U G) := by
  classical
  let W : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | P ∈ holSub (U σ).X (modelWt (U σ) G) ∧ ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0}
      add_mem' := fun {P Q} hP hQ => ⟨add_mem hP.1 hQ.1, fun k x hx => by
        change P k x + Q k x = 0
        rw [hP.2 k x hx, hQ.2 k x hx, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun k x hx => rfl⟩
      smul_mem' := fun t P hP => ⟨Submodule.smul_mem _ t hP.1, fun k x hx => by
        change t • P k x = 0
        rw [hP.2 k x hx, smul_zero]⟩ }
  haveI : FiniteDimensional ℂ W :=
    GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain E r (U σ).Comp (U σ).X (modelWt (U σ) G) W (fun P hP => hP.1) (fun P hP => hP.2)
  have key : ∀ s : Finset (cuspW Xo c U G),
      LinearIndependent c.F (fun i : s => (i : cuspW Xo c U G)) → s.card ≤ Module.finrank ℂ W := by
    intro s hs
    let e := s.equivFin
    have h0 : LinearIndependent c.F (fun j : Fin s.card => ((e.symm j : s) : cuspW Xo c U G)) :=
      hs.comp (fun j => e.symm j) e.symm.injective
    have hb : LinearIndependent c.F
        (fun j : Fin s.card => (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c)) :=
      h0.map' (cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := reading_linearIndependent_secZ hS (U σ) hU (exZ Dw G) s.card _
      (fun j => cuspW_le_secZ G ((e.symm j : s) : cuspW Xo c U G).2) hb
    have hmem : ∀ j : Fin s.card,
        rdU (U σ) (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c) ∈ W :=
      fun j => ⟨(mem_cuspW.1 ((e.symm j : s) : cuspW Xo c U G).2).2 σ hσ, fun k x hx => by
        simp [rdU, hx]⟩
    let b' : Fin s.card → W := fun j => ⟨_, hmem j⟩
    have hc' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype hc
    have := hc'.fintype_card_le_finrank
    simpa using this
  haveI : Module.Free c.F ↥(cuspW Xo c U G) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp ((rank_le key).trans_lt (Cardinal.natCast_lt_aleph0))

end GlobalTheory

theorem GlobalTheory.Deep.finiteDimensional_V_of_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, FiniteDimensional Y.d.c₂.F (Y.V G) := by
  intro D T j Y e o hY G
  have hσ : Formalism.L2.Pj.GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom) :=
    Formalism.L2.Pj.goodEmb_goodOf _ _
  exact GlobalTheory.cuspW_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ (hY.unf _ hσ) G
end

