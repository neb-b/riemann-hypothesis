module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

def avgC {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra ℂ G :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ h : G, MonoidAlgebra.of ℂ G (h * g * h⁻¹)

theorem center_eq_sum {G : Type} [Group G] [Fintype G] (z : MonoidAlgebra ℂ G)
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : z = ∑ g : G, z.coeff g • avgC g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ = z := by
    intro h
    rw [hz, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h2 : z = ∑ g : G, z.coeff g • MonoidAlgebra.of ℂ G g := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc z = (Fintype.card G : ℂ)⁻¹ • ∑ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ := by
        simp only [h1, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = ∑ g : G, z.coeff g • avgC g := by
        conv_lhs => rw [h2]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, avgC, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        rw [← map_mul, ← map_mul, smul_comm]

theorem avgC_mem {G : Type} [Group G] [Fintype G] (g : G) : avgC g ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgC, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

def avgK (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra K G :=
  ((Fintype.card G : K)⁻¹) • ∑ h : G, MonoidAlgebra.of K G (h * g * h⁻¹)

theorem avgK_coeff {K : Type} [Field K] {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (e : G ≃* H)
    (g y : G) : σ ((avgK K g).coeff y) = (avgC (e g)).coeff (e y) := by
  simp only [avgK, avgC, MonoidAlgebra.of_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, map_mul, map_inv₀,
    map_natCast, map_sum, apply_ite, map_one, map_zero]
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_inv]
  classical
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hy : h * g * h⁻¹ = y
  · rw [if_pos hy, if_pos (congrArg e hy), map_one]
  · rw [if_neg hy, if_neg (fun h' => hy (e.injective h')), map_zero]

theorem lin_center {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    (Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₗ[ℂ] W) (v : G → W)
    (h : ∀ g₁, Φ ⟨avgC g₁, avgC_mem g₁⟩ = ∑ g₀, (avgC g₁).coeff g₀ • v g₀)
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    Φ z = ∑ g₀, (z : MonoidAlgebra ℂ G).coeff g₀ • v g₀ := by
  have hz : z = ∑ g₁, (z : MonoidAlgebra ℂ G).coeff g₁ •
      (⟨avgC g₁, avgC_mem g₁⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [SetLike.val_smul]
    exact center_eq_sum _ z.2
  conv_lhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [center_eq_sum _ z.2]
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.coe_finsetSum, Finset.sum_apply]

theorem avgK_comm (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) (b : MonoidAlgebra K G) :
    b * avgK K g = avgK K g * b := by
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgK, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem avgK_conj (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g c y : G) :
    (avgK K g).coeff (c * y * c⁻¹) = (avgK K g).coeff y := by
  classical
  simp only [avgK, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun h => ?_).symm
  rw [Finsupp.single_apply, Finsupp.single_apply]
  refine if_congr ⟨fun e => ?_, fun e => ?_⟩ rfl rfl
  · rw [← e]; simp [mul_assoc]
  · have e' : c * (h * g * h⁻¹) * c⁻¹ = c * y * c⁻¹ := by rw [← e]; simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel e')

theorem actSum_apply (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : Formalism.AUTREP.GAf D.host.E n → W) (g : Formalism.AUTREP.GAf D.host.E n) :
    GlobalTheory.PendOf.actSum D L z f g = ∑ g₀ : G0g D.nd, z.coeff g₀ • f (g * L g₀) := by
  unfold GlobalTheory.PendOf.actSum
  rw [Finsupp.sum_fintype _ _ (by intros; simp)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

section Rows

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)

def ratForm (k : Fin D.R.m) (s : T) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) :=
  D.what₂.jMt (Y.tup s) ((k : ℕ) + 1) (Y.eMt k s x)


variable (F) in
def lvlAct (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL :=
  ((A3.A.fam.L k s).S.lvlOp (A3.A.fam.L k s).r (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).P (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).ψ a).mulVec x

def adForm (μ : D.what₂.Tup) (h : Used0 D μ) (k : Fin D.R.m) :
    D.what₂.Mt μ ((k : ℕ) + 1) →ₗ[ℂ] (GA D (Vc D k) → (R.cV k).W) where
  toFun x := (Y.IL.jMt μ h k x).1
  map_add' x y := by rw [map_add (f := _)]; rfl
  map_smul' c x := by rw [map_smul]; rfl

def CenRat : Prop :=
  ∀ (s : T) (k : Fin D.R.m) (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) →
    ∀ x, D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z (ratForm Y k s x) = ratForm Y k s (lvlAct F k s a x)

def ActRead : Prop :=
  ∀ (s : T) (h : Used0 D (Y.tup s)) (k : Fin D.R.m) (a : MonoidAlgebra D.what₂.LL G), (∀ b, b * a = a * b) →
    ∀ κ : G → GA D (Vc D k), (∀ g, Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (κ g)) →
    ∀ x y, adForm Y (Y.tup s) h k (ratForm Y k s (lvlAct F k s a x)) y =
      ∑ g : G, (D.what₂.embLL (a.coeff g) * (Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (κ g))⁻¹) •
        adForm Y (Y.tup s) h k (ratForm Y k s x) (y * κ g)

def FrameAt (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV) (s : T) : Prop :=
  ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
    (Nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) → ∃ c : G, ∀ g : G,
      Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
      Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1)


set_option maxHeartbeats 1000000 in
theorem cenLoc_of (M : MtFam D) (ad : MtAd Y M) (h1 : CenRat Y cG) (h2 : ActRead Y)
    (h3 : ∀ (i : D.nd.Loc) (s : T) (k : Fin D.R.m), Y.tup s = D.nd.mu i → FrameAt Y cG k (ad.PV k) s) : CenLoc D M := by
  intro i
  suffices H : ∀ μ, Used0 D μ → ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m),
      (∀ (s : T) (k : Fin D.R.m), Y.tup s = μ → FrameAt Y cG k (ad.PV k) s) →
      ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
        ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
          (M μ j hj1 hj2).real (D.ntypes.cenMt μ j z x) =
            GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j hj1 hj2).real x) from
    H _ (Model.used_loc i) _ (D.nd.j_range i).1 (D.nd.j_range i).2 (h3 i)
  intro μ hμ j hj1 hj2 h3
  obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, Y.tup s = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨L, hL, hc⟩ := h3 s k rfl
  refine ⟨L, hL, fun z x => funext fun g => ?_⟩
  rw [actSum_apply]
  rcases subsingleton_or_nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) with h0 | h0
  · rw [Subsingleton.elim x 0]; simp
  obtain ⟨c, hc⟩ := hc h0
  have key : ∀ g₁ : G0g D.nd,
      adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ x) ((ad.PV k).ψ g) =
        ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀)) := by
    intro g₁
    have tie : ∀ y, D.what₂.embLL ((avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff y) = (avgC g₁).coeff ((R.eG.trans cG) y) :=
      fun y => by rw [avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      (LinearMap.proj ((ad.PV k).ψ g)).comp ((adForm Y (Y.tup s) hμ k).comp
        (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩))
    let F2 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      { toFun := fun y => ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k y ((ad.PV k).ψ (g * L g₀))
        map_add' := fun y y' => by simp only [map_add (f := _), Pi.add_apply, smul_add, Finset.sum_add_distrib]
        map_smul' := fun c y => by
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _ }
    have hb := (D.what₂.jMt_basis (Y.tup s) ((k : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt k s).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)) b)
      rw [← hx']
      show adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ (ratForm Y k s x'))
        ((ad.PV k).ψ g) = ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k (ratForm Y k s x') ((ad.PV k).ψ (g * L g₀))
      rw [h1 s k ⟨avgC g₁, avgC_mem g₁⟩ _ tie x', h2 s hμ k _ (avgK_comm _ _) _ (fun y => (hc y).1) x']
      refine Fintype.sum_equiv ((MulAut.conj c).toEquiv.trans (R.eG.trans cG).toEquiv) _ _ fun y => ?_
      rw [(hc y).2, inv_one, mul_one, ← avgK_conj _ _ c y, tie, ← map_mul]
      rfl
    exact LinearMap.congr_fun hF x
  apply (ad.eW _ hμ k).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ad.read, map_sum]
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV k).W :=
    { toFun := fun z' => adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z' x) ((ad.PV k).ψ g)
      map_add' := fun y y' => by simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c y => by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  refine (lin_center Φ (fun g₀ => adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀))) key z).trans ?_
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [map_smul, ad.read]
  rfl

end Rows

end GlobalTheory.CenLocAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInvStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η = -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_lie | exact GlobalTheory.PointChern.curv_modelGram_lie | (intros; apply GlobalTheory.PointChern.curv_modelGram_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernRootSubstitutionWeightLineBundleEqLinRoot
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagRoot_term_big {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.p) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩ =
      -(C ((la τ (Fin.castAdd Dw.q i) : ℤ) : ℝ) * X (τ, Fin.castAdd Dw.q i)) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (τ.1, (i : ℕ)) := rfl
  rw [he, GlobalTheory.AllWt.wtOf_big la 0 τ i i.2]
  unfold flagRoot
  rw [dite_eq_left τ.2]
  simp only [sub_zero, map_neg, neg_mul, neg_neg]
  rfl

theorem flagRoot_term_small {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.q) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0
          (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩ =
      -(C ((la τ (Fin.natAdd Dw.p (Fin.rev i)) : ℤ) : ℝ) * X (τ, Fin.natAdd Dw.p (Fin.rev i))) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0
      (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (conjEmb τ.1, (i : ℕ)) := rfl
  have hj : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p (Fin.rev i) := by
    ext; simp [Fin.val_rev]; omega
  rw [he, GlobalTheory.AllWt.wtOf_small la 0 τ i i.2, hj]
  unfold flagRoot
  rw [dite_eq_right (GlobalTheory.AllWt.conj_not_mem τ)]
  have hτ : (⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  have hx : ((⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H),
      (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q))) = (τ, Fin.natAdd Dw.p (Fin.rev i)) := by
    rw [hτ, hj]
  simp only [Fin.val_cast] at *
  rw [hx]
  simp only [sub_zero, Int.cast_neg, neg_neg, mul_neg]

theorem chernRootSubstitution_weightLineBundle_eq_linRoot (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) :
    flagMap Dw (∑ x : GlobalTheory.GoodMetric.Root Dw.mult,
        MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) =
      Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [flagMap, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
  rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  let e : GlobalTheory.AllWt.Psi H ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  rw [← e.sum_comp]
  unfold Formalism.DegreeFormula.linRoot
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨τ.1, i⟩)
      (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_big Dw la τ i
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change ∑ i : Fin (Dw.mult (conjEmb τ.1)), C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩ = _
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩) (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm,
      ← Equiv.sum_comp (Fin.revPerm (n := Dw.q)) (fun i => C ((la τ (Fin.natAdd Dw.p i) : ℤ) : ℝ) *
        X (τ, Fin.natAdd Dw.p i)), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_small Dw la τ i

end GlobalTheory.Schubert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffMatrixMulEqOfSameIntCombinations
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameFix

theorem coeff_mul_eq_of_same_combinations :
    ∀ (g r r₀ : ℕ) (l l' : Fin r → Fin g → ℂ) (w : Fin r₀ → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ)
      (T : Matrix (Fin r) (Fin r) ℤ), LinearIndependent ℤ l → (∀ i, l' i = ∑ j, T i j • l j) →
      (∀ i, w i = ∑ j, c i j • l j) → (∀ i, w i = ∑ j, c i j • l' j) → c * T = c := by
  intro g r r₀ l l' w c T hl hl' h1 h2
  ext i m
  have key : ∑ j, c i j • l' j = ∑ m, (c * T) i m • l m := by
    simp only [hl', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hsum : ∑ m, ((c * T) i m - c i m) • l m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← key, ← h2, h1, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hl (fun m => (c * T) i m - c i m) hsum m)

end GlobalTheory.FrameFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexMatrixEqOfHermFormImEqRealSpan
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_eq_of_im_eq_on_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  intro g r Hm Hm' l hspan h
  have h1 : ∀ z, ∀ j, (hermForm Hm z (l j)).im = (hermForm Hm' z (l j)).im := by
    intro z j
    have hz : z ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm Hm z w).im = (hermForm Hm' z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ (Set.range l) := hspan ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact h1 z j
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoords
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan

theorem cone_match_rays_of_nonneg {X : Type} [AddCommGroup X] {m₀ : ℕ}
    (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hp : LinearIndependent ℤ (fun i : {i // 0 < t i} => p i))
    (β : LinearMap.BilinForm ℤ X) (hβ : toReal β = ∑ i, t i • toReal (p i))
    (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (hδ : LinearIndependent ℤ δ)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hβ' : toReal β = ∑ j, c j • toReal (δ j))
    (h1 : ∀ i, 0 < t i → InRCone δ (p i))
    (h2 : ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
      toReal (δ j) = ∑ i, a i • toReal (p i)) :
    (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧
      c j = t i * d) := by
  classical
  set e := (Fintype.equivFin {i // 0 < t i}).symm with he
  have key : ∀ a : Fin m₀ → ℝ, (∀ i, t i = 0 → a i = 0) →
      ∑ i', a (e i') • toReal (p (e i')) = ∑ i, a i • toReal (p i) := by
    intro a ha
    refine Fintype.sum_of_injective (fun i' => ((e i' : {i // 0 < t i}) : Fin m₀))
      (Subtype.val_injective.comp e.injective) _ _ ?_ (fun _ => rfl)
    intro i hi
    have : t i = 0 := by
      by_contra h0
      exact hi ⟨e.symm ⟨i, lt_of_le_of_ne (ht i) (Ne.symm h0)⟩, by simp⟩
    rw [ha i this, zero_smul]
  obtain ⟨r1, r2⟩ := _root_.GlobalTheory.PolFan.cone_match_rays (fun i' => p (e i')) δ (hp.comp e e.injective) hδ
    (fun i' => t (e i')) c (fun i' => (e i').2) hc
    (by rw [key t (fun _ h => h), ← hβ, hβ'])
    (fun i' => h1 _ (e i').2)
    (fun j hj => by
      obtain ⟨a, ha0, ha1, ha2⟩ := h2 j hj
      exact ⟨fun i' => a (e i'), fun i' => ha0 _, by rw [ha2, ← key a ha1]⟩)
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simpa using r1 (e.symm ⟨i, hi⟩)
  · obtain ⟨i', h⟩ := r2 j hj
    exact ⟨e i', (e i').2, h⟩

end GlobalTheory.PolFan
end

