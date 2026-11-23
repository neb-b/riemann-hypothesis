module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)


set_option smartUnfolding false in
set_option maxHeartbeats 4000000 in
def reY {X : HidaSetting D} (Y : Full X) : Full (reX Z X) where
  hK := (Y.hK)
  TR := (reTR Z Y.TR)
  psi_ne := (Y.psi_ne)
  what₂ := (Y.what₂)
  rowsOK := (Y.rowsOK)
  split := (Y.split)
  cs := (fun (u : @Formalism.BasicNotions.Rows.Data.Word (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D)) ↦ @GlobalTheory.Mem.SRe.reCS D Z X u (@Formalism.L2.SG.Full.Full.what₂ D X Y u) (@Formalism.L2.SG.Full.Full.cs D X Y u))
  colReps := (Y.colReps)
  Dt := (Y.Dt)
  reps := (Y.reps)
  FN := (Y.FN)
  FN_fund := (Y.FN_fund)
  δ := (Y.δ)
  M := (Y.M)
  agree := (Y.agree)
  δ_pin := (Y.δ_pin)


set_option maxHeartbeats 4000000 in
def eRT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : RT Y u u' ≃ RT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)


set_option maxHeartbeats 4000000 in
def eTT {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) : TT Y u u' ≃ TT (reY Z Y) (wd Z u) (wd Z u') where
  toFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  invFun t := ⟨(t.lam), (t.mem), (t.lam'), (t.mem'), (t.cls)⟩
  left_inv t := (Eq.refl t)
  right_inv t := (Eq.refl t)


set_option maxHeartbeats 4000000 in
def eCure {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y)) (u : D.what₂.Word) :
    ColT (h.shInj u) ≃ₗᵢ[ℂ] ColT (h'.shInj (wd Z u)) := by
  run_tac
    let h := Lean.mkIdent `h
    let u := Lean.mkIdent `u
    let e ← Lean.Elab.Term.elabTerm (← `(LinearIsometryEquiv.refl ℂ (ColT (($h).shInj $u)))) none
    (← Lean.Elab.Tactic.getMainGoal).assign e
    Lean.Elab.Tactic.replaceMainGoal []

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingOneApplyDivThree
section
noncomputable section

open Formalism.BasicNotions NumberField Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.Mem.R3.MjModel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem unitMap_norm (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (x : (unitLat K (Module.finrank ℂ W)).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X
      (InfinitePlace.mk σ) x) = ‖unitMap σ W x‖ := by
  have h1 : unitMap σ W x = ∑ i, σ (x i) • stdOrthonormalBasis ℂ W i :=
    Fintype.linearCombination_apply ℂ (stdOrthonormalBasis ℂ W) (cpt σ x)
  have h2 : ‖unitMap σ W x‖ ^ 2 = ∑ i, ‖σ (x i)‖ ^ 2 := by
    rw [← (stdOrthonormalBasis ℂ W).sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1, (stdOrthonormalBasis ℂ W).orthonormal.inner_right_fintype]
  rw [← Real.sqrt_sq (norm_nonneg (unitMap σ W x)), h2, Formalism.HermitianLatticesTheory.cnorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : Formalism.HermitianLatticesTheory.fcoord (unitLat K (Module.finrank ℂ W)).b (unitLat K (Module.finrank ℂ W)).X (InfinitePlace.mk σ) x i =
      (InfinitePlace.mk σ).embedding (x i) := by
    have h4 : ∀ (n : ℕ) (u : Fin n → ℂ), Matrix.mulVec (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ u = u := fun n u => by
      rw [inv_one, Matrix.one_mulVec]
    exact congrFun (h4 _ _) i
  rw [h3, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

section Record

open Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)

theorem jM_metric_all (hH : Holds R F) (j : ℕ) (x : (mjH Z j).V) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (mjH Z j).b (mjH Z j).X (InfinitePlace.mk D.what₂.embLL) x) = ‖jM Z j x‖ :=
  mapSeq_ind_all _ _ D.what₂.Mj Z.jW
    (fun _ A g => ∀ x : A.V, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord A.b A.X (InfinitePlace.mk D.what₂.embLL) x) = ‖g x‖)
    (fun i => MjCoord.jW_norm Z hH i) (fun _ => unitMap_norm _ _) j x

end Record

end GlobalTheory.Mem.R3.MjModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsLabOfOrder
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable {g : ℕ} [Fact g.Prime]

theorem eq_one_of_cong (h : IsPlaceOver A w) (hw : normV w = g) {l : ℕ} (hc : l.Coprime g)
    {u : Ω} (hu : u ^ l = 1) (h1 : A.valuation (u - 1) < 1) : u = 1 := by
  have hg : g.Prime := Fact.out
  by_contra hne
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [Nat.Coprime, Nat.gcd_zero_left] at hc
    exact hg.ne_one hc
  have hv : A.valuation u ≤ 1 := by
    have := A.valuation.map_add (u - 1) 1
    rw [sub_add_cancel, map_one] at this
    exact this.trans (max_le h1.le le_rfl)
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have e := geom_sum_mul u l
    rw [hu, sub_self] at e
    exact (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hne)
  have hlv : A.valuation (l : Ω) < 1 := by
    have e : (l : Ω) = -∑ i ∈ Finset.range l, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [e, Valuation.map_neg]
    exact Valuation.map_sum_lt _ one_ne_zero fun i _ => by
      simpa using GlobalTheory.WeilDeligne.cong_pow hv (by simp) h1 i
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hw]
    have : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (by
      rw [show Nat.card (𝓞 E ⧸ w.asIdeal) = normV w from rfl, hw]
      exact hg.ne_zero)
    rw [show normV w = Nat.card (𝓞 E ⧸ w.asIdeal) from rfl, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    intro hl
    obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hc).map (Int.castRingHom (𝓞 E))
    have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
      rw [← hab]
      simp only [eq_intCast, Int.cast_natCast]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hl) (w.asIdeal.mul_mem_left b hgw)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have := GlobalTheory.InertiaMovesRoot.val_eq_one_of_notMem h hlw
  have e : algebraMap E Ω ((((l : ℕ) : 𝓞 E)) : E) = (l : Ω) := by simp
  rw [e] at this
  exact (ne_of_lt hlv) this

end GlobalTheory.WeilDeligne.LabModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts Formalism.BasicNotions

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.TrueGeo

def cxSt (F : Type) [Field F] [NumberField F] : CxSt F := ProjVar.cxStage F

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv}

end GlobalTheory.TrueGeo
end
end

