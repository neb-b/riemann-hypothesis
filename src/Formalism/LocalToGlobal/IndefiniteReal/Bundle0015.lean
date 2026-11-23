module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.GlobalTheory.DivPassage
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) where
  A : FamIn K G Pl0 T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)
  Zsc : DefSub A.fam.amb → IndefScale A.fam.base
  X : CxData A.fam.amb
  gE : Representation ℂ G X.EE

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

abbrev cr : Crd I.A.fam.amb (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A.fam.amb (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A.fam.base.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A.fam.base.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A.fam.base.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A.fam.base.Tup) :
    Matrix (Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A.fam.base.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))


open Classical in
def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

structure Hyp (s : ℕ) : Prop where
  ok : I.A.fam.Ok s
  sep : I.A.fam.TypesSep
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A.side I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A.side I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : GUnit I.A I.X I.gE
  gequiv : GEquiv I.A I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A.fam.base.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A.fam.base.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

end In

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.EquivFunOM
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition

namespace GroupActionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms} {I : Type}

def oM (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (op i)

structure OkOp (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) : Prop where

  rat : ∀ i a b, oM B op i a b ∈ cmMax K

  adj : ∀ i, ∃ i', ∀ f g : B.S.Forms,
    B.S.csum (op i f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = B.S.csum (f : B.S.Cl → B.S.V) (op i' g : B.S.Cl → B.S.V)

  comm : Col.PairComm op

  split : Col.SplitOver op

  opG : ∀ i g, Commute (op i) (B.r g)

variable {op : I → Module.End K B.S.Forms}

theorem equivFun_oM (i : I) (f : B.S.Forms) :
    B.S.basis.equivFun (op i f) = (oM B op i).mulVec (B.S.basis.equivFun f) := by
  exact equivFun_end (op i) f

theorem oM_comm (hc : Col.PairComm op) (i j : I) : oM B op i * oM B op j = oM B op j * oM B op i := by
  simp only [oM]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]

private theorem okH_of_okOp (hO : OkOp B op) : BlockDat.OkH ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) :=
  { rat := fun p a b => hO.rat p.1 a b
    adj := fun p => by
      obtain ⟨i', hi'⟩ := hO.adj p.1
      exact ⟨(i', 0), hi'⟩ }

theorem oM_adj (hO : OkOp B op) (i : I) : ∃ i', (oM B op i)ᴴ * B.S.H = B.S.H * oM B op i' := by
  obtain ⟨i', hi'⟩ := opMat_adj (okH_of_okOp hO) (i, 0)
  exact ⟨i'.1, hi'⟩

private theorem blockHyp_of_okOp (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) : BlockHyp ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) ℓ v0 s :=
  { conj := h.conj
    irr := h.irr
    ok :=
    { good := h.ok.good
      hrat := h.ok.hrat
      hpos := h.ok.hpos
      act := h.ok.act
      actRat := h.ok.actRat
      comm := fun p q => hO.comm p.1 q.1
      split := fun p => hO.split p.1
      opG := fun p g => hO.opG p.1 g
      blocks := ⟨le_rfl, List.cons_ne_nil _ _, by simp⟩
      q_pos := fun _ => Nat.one_pos
      pl_inj := Function.injective_id } }

private theorem eigSum_prod_nat_eq_eigSum (C : (I → K) → Prop) :
    Col.eigSum (fun p : I × ℕ => op p.1) (fun y => C (fun i => y (i, 0))) = Col.eigSum op C := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => le_trans ?_ (le_iSup₂ (f := fun x (_ : C x) => Col.eigAt op x) _ hy)
    exact le_iInf fun i => iInf_le (fun p : I × ℕ => (op p.1).maxGenEigenspace (y p)) (i, 0)
  · refine iSup₂_le fun x hx => ?_
    have h2 : Col.eigAt op x ≤ Col.eigAt (fun p : I × ℕ => op p.1) (fun p => x p.1) :=
      le_iInf fun p => iInf_le (fun i => (op i).maxGenEigenspace (x i)) p.1
    refine h2.trans ?_
    unfold Col.eigSum
    refine le_trans ?_ (le_iSup _ (fun p : I × ℕ => x p.1))
    exact le_iSup_of_le (show C (fun i => x i) from hx) le_rfl

theorem eig_ratG (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (C : (I → K) → Prop) :
    SubHasRatBasis (B.inV0 ℓ (Col.eigSum op C)) := by
  have h1 := eig_rat (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun y => C (fun i => y (i, 0)))
  rw [eigSum_prod_nat_eq_eigSum] at h1
  exact h1

def tVg (B : BlockDat K G Pl0) (ℓ : Lvl K G) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin (B.nV ℓ)) (Fin (B.nV ℓ)) K :=
  B.vPr ℓ * oM B op i * B.vE ℓ

theorem vE_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i : I) : B.vE ℓ * tVg B ℓ op i = oM B op i * B.vE ℓ := by
  exact vE_tV (blockHyp_of_okOp h hO) (i, 0)

theorem tVg_comm (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i j : I) : tVg B ℓ op i * tVg B ℓ op j = tVg B ℓ op j * tVg B ℓ op i := by
  exact tV_comm (blockHyp_of_okOp h hO) (i, 0) (j, 0)

theorem Pq_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (i : I) :
    B.Pq ℓ Z * tVg B ℓ op i = (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z) * B.Pq ℓ Z := by
  exact Pq_tV (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun p => hZ p.1) (i, 0)

theorem adjCg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (σ : K →+* ℂ) (i : I) :
    ∃ i', (B.HV ℓ).map σ * (tVg B ℓ op i).map σ = ((tVg B ℓ op i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := adjC (blockHyp_of_okOp h hO) (okH_of_okOp hO) σ (i, 0)
  exact ⟨i'.1, hi'⟩

theorem part_orthg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (v : InfinitePlace K)
    {C C' : (I → K) → Prop} (hSS : ∀ x, C' x → ¬ C x)
    {x y : Fin (B.dZ ℓ Z) → K} (hx : x ∈ (B.inV0 ℓ (Col.eigSum op C)).comap (B.zE ℓ Z).mulVecLin)
    (hy : y ∈ (B.inV0 ℓ (Col.eigSum op C')).comap (B.zE ℓ Z).mulVecLin) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = 0 := by
  have hA : ((B.HV ℓ).map v.embedding).PosDef := BlockDat.lf_HV_pos h v
  have hc : Col.PairComm (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (tVg_comm h hO i j)
    simpa only [Matrix.map_mul] using e
  have hs : Col.SplitOver (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hcf : Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (oM_comm hO.comm i j)
    simpa only [Matrix.map_mul] using e
  have hvv : B.vPr ℓ * B.vE ℓ = 1 := (BlockDat.lf_v_proj h).1.1

  have key : ∀ {D : (I → K) → Prop} {w : Fin (B.dZ ℓ Z) → K},
      w ∈ (B.inV0 ℓ (Col.eigSum op D)).comap (B.zE ℓ Z).mulVecLin →
      (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) ∈ Col.eigSum (linF fun i => (tVg B ℓ op i).map v.embedding)
        (fun y => ∃ x, D x ∧ y = fun i => v.embedding (x i)) := by
    intro D w hw
    have h1 : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w) ∈ Col.eigSum (fun i => Matrix.toLin' (oM B op i)) D := by
      have hw' : (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVecLin w) ∈ B.coord (Col.eigSum op D) := hw
      obtain ⟨F, hF, hFe⟩ := Submodule.mem_map.1 hw'
      have h3 := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i))
        (fun i f => by simp only [LinearEquiv.coe_coe, equivFun_oM, Matrix.toLin'_apply]) D hF
      rw [Submodule.mem_comap, hFe] at h3
      simpa only [Matrix.mulVecLin_apply] using h3
    have h2 := emb_mem_eigSum v.embedding (oM B op) D h1
    refine mem_eigSum_of_emb _ _ ((B.vE ℓ).map v.embedding) ((B.vPr ℓ).map v.embedding)
      (by rw [← Matrix.map_mul, hvv, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i => by
        have e := congrArg (fun M => M.map v.embedding) (vE_tVg h hO i)
        simpa only [Matrix.map_mul] using e) hc hs hcf _ ?_
    have e : (B.vE ℓ).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) =
        fun a => v.embedding ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w)) a) := by
      ext a
      exact (RingHom.map_mulVec _ _ _ _).symm
    rw [e]
    exact h2
  have hx' := key hx
  have hy' := key hy
  have hCC : ∀ y, (fun y => ∃ x, C' x ∧ y = fun i => v.embedding (x i)) y →
      ¬ (fun y => ∃ x, C x ∧ y = fun i => v.embedding (x i)) y := by
    rintro y ⟨x', hx1, rfl⟩ ⟨x, hx2, hxx⟩
    have hxe : x = x' := funext fun i => v.embedding.injective (congrFun hxx i).symm
    exact hSS x' hx1 (hxe ▸ hx2)
  have hPN : ∀ i, (B.Pq ℓ Z).map v.embedding * (tVg B ℓ op i).map v.embedding =
      (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z).map v.embedding * (B.Pq ℓ Z).map v.embedding := fun i => by
    have e := congrArg (fun M => M.map v.embedding) (Pq_tVg h hO hZ i)
    simpa only [Matrix.map_mul] using e
  have hPz : B.Pq ℓ Z * B.zE ℓ Z = 1 := (pq_orth (Z := Z) h).1
  have hPu : ∀ w : Fin (B.dZ ℓ Z) → K,
      (B.Pq ℓ Z).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) = fun a => v.embedding (w a) := by
    intro w
    ext a
    have e := (RingHom.map_mulVec v.embedding (B.Pq ℓ Z) (B.zE ℓ Z *ᵥ w) a).symm
    rw [Matrix.mulVec_mulVec, hPz, Matrix.one_mulVec] at e
    exact e
  have hq : IsQuotMetric (B.Pq ℓ Z) (B.HV ℓ) (B.XQ ℓ Z) := BlockDat.XQ_quot h.conj h.ok h.irr
  have hvx : ∀ w : Fin (B.dZ ℓ Z) → K,
      Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin (B.dZ ℓ Z))) v w = fun a => v.embedding (w a) := fun w => by
    ext a
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [Formalism.HermitianLatticesTheory.majBasic_majAt, (hq v).2, hvx, hvx]
  by_cases hR : IsUnit ((B.Pq ℓ Z).map v.embedding * ((B.HV ℓ).map v.embedding)⁻¹ *
      ((B.Pq ℓ Z).map v.embedding)ᴴ).det
  · have e := cx_quot_orth (hA := hA) (adj := adjCg h hO v.embedding) (hPN := hPN) (hR := hR) (hc := hc)
      (hs := hs) (hCC := hCC) (hu := hx') (hu' := hy')
    rw [hPu, hPu] at e
    exact e
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hR]
    simp

end GroupActionMatrices

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField Formalism.IndefR.DeterminantProjection Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

variable {D : D7}

abbrev sigE (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sigE_sigE (a : D.host.E) : sigE D (sigE D a) = a := star_star a

theorem gram_herm (V : HSp D) (i j : Fin V.rank) : sigE D (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem cA_incA' (a : D.host.E) : cA D (incA D a) = incA D (sigE D a) := by
  simp [cA, incA, sigR, inclR]

theorem gramA_herm (V : HSp D) (i j : Fin V.rank) :
    cA D (V.gram.map (incA D) i j) = V.gram.map (incA D) j i := by
  simp only [Matrix.map_apply, cA_incA', gram_herm]

def mkGA (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) : GA D V :=
  let g : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨Matrix.nonsingInvUnit M hd, hM⟩
  g

theorem aniso_data (V : HSp D) (hn : 0 < V.rank) :
    ∃ (u : Fin V.rank → D.host.E) (ainv : D.host.E), ainv * hsq (sigE D) V.gram u = 1 ∧ sigE D ainv = ainv := by
  have : Nonempty (Fin V.rank) := ⟨⟨0, hn⟩⟩
  obtain ⟨u, hu⟩ := exists_aniso (sigE D) sigE_sigE V.gram (gram_herm V) (gram_det_ne V)
  refine ⟨u, (hsq (sigE D) V.gram u)⁻¹, inv_mul_cancel₀ hu, ?_⟩
  rw [map_inv₀, sigma_hsq (sigE D) sigE_sigE V.gram (gram_herm V) u]

theorem exists_GA_det (V : HSp D) (hn : 0 < V.rank) (x : AE D) (hx : cA D x * x = 1) (hxu : IsUnit x) :
    ∃ (R : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (g : GA D V), mt V g = 1 + (x - 1) • R ∧ (mt V g).det = x := by
  obtain ⟨u, ainv, ha, hainv⟩ := aniso_data V hn
  have haA : incA D ainv * hsq (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) = 1 := by
    rw [← hsq_map (incA D) (sigE D) (cA D) (fun a => (cA_incA' a).symm), ← map_mul, ha, map_one]
  have hainvA : cA D (incA D ainv) = incA D ainv := by rw [cA_incA', hainv]
  set R := proj (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv)
  have hM := proj_unitary (cA D) cA_cA (V.gram.map (incA D)) (gramA_herm V) (fun i => incA D (u i))
    (incA D ainv) haA hainvA x hx
  have hdet := det_proj' (cA D) (V.gram.map (incA D)) (fun i => incA D (u i)) (incA D ainv) haA x
  exact ⟨R, mkGA V _ hM (by rw [hdet]; exact hxu), rfl, hdet⟩

theorem splitDet : SplitDetP := by
  intro D V hn e he x hx hsupp
  obtain ⟨R, g, hg, hdet⟩ := exists_GA_det V hn (x : AE D) (by rw [mul_comm]; exact hx) x.isUnit
  refine ⟨g, ?_, ?_, hdet⟩
  · intro i j
    rw [hg, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    unfold SuppAtU at hsupp
    rw [hsupp]
  · have hxi : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := x.mul_inv
    set xi : AE D := ((x⁻¹ : (AE D)ˣ) : AE D) with hxi_def
    set x0 : AE D := (x : AE D) with hx0
    have p1 : (e * x0 + (1 - e)) * (e * xi + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    have p2 : (e * xi + (1 - e)) * (e * x0 + (1 - e)) = 1 := by
      linear_combination (x0 * xi - x0 - xi + 1) * he.1 + e * hxi
    obtain ⟨y, hy⟩ : ∃ y : (AE D)ˣ, (y : AE D) = e * x0 + (1 - e) := ⟨⟨_, _, p1, p2⟩, rfl⟩
    refine ⟨y, ?_⟩
    unfold IsDetAt
    rw [hy, hdet]

end Formalism.IndefR.flipTwoThree

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IsThPKernelSigBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


variable (D) in
def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

theorem labE_base (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  have h := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) x)
  simpa [labE, labLL, tauE, Host.emb] using h

structure ArchLab (D : D7) where
  perm : D.what₂.Tau ≃ D.what₂.Tau
  side : Bool

def ArchLab.emb (A : ArchLab D) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  if A.side then tauE D (A.perm τ) else (starRingEnd ℂ).comp (tauE D (A.perm τ))

def IsLabOf (σ : D.what₂.LL →+* ℂ) (A : ArchLab D) : Prop := ∀ τ, labE σ τ = A.emb τ



variable (D) in
def LabExists : Prop := ∀ σ : D.what₂.LL →+* ℂ, ∃ A : ArchLab D, IsLabOf σ A




end Formalism.IndefR.Conj

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PHeisThP
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

abbrev Ix {D : D7} (V W : HSp D) : Type := Fin V.rank × Fin W.rank × Fin (nE D)

def Co {D : D7} (V W : HSp D) (x : WA V W) (a : Ix V W) : AF D.host.F := Phi V W x a.1 a.2.1 a.2.2

def CoordFinP : Prop :=
  ∀ (D : D7) (V W : HSp D) (x : WA V W), x.map (finPart D) = 0 → ∀ a, (Co V W x a).2 = 0



def PsiOpenP : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∃ G : AddSubgroup (Af F), IsOpen (G : Set (Af F)) ∧ (∀ y ∈ G, ∀ z ∈ Ohat F, z * y ∈ G) ∧
      ∀ y ∈ G, ψ (pairA F 0 y) = 1

def PsiSmoothP : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (k : ℕ) (s : (Fin k → ℝ) →+ Ainf D.host.F), Continuous s →
      ContDiff ℝ ∞ fun t => ψ (pairA D.host.F (s t) 0)

end Formalism.IndefR.PHeisTh

end
end

