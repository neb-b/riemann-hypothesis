module

public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

@[expose] public section

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.HermitianLatticesTheory

namespace Formalism.L2.DIV.RatFullPt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

private theorem span_of_scaled_dual {K : Type} [Field K] [NumberField K] [StarRing K]
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hfg : M.FG) {c : 𝓞 K} (hc : c ≠ 0)
    (hdual : ∀ x ∈ dual (hform H) M, c • x ∈ M) :
    Submodule.span K (M : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨generators, hgen⟩ := hfg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    generators (fun y => hform H y x)
  have hmem : (d : 𝓞 K) • x ∈ dual (hform H) M := by
    rw [mem_dual_iff]
    intro y hy
    rw [← hgen] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rw [← algebraMap_smul K, LinearMap.map_smul, algebraMap_smul K]
        exact Submodule.mem_one.mpr (hd y hy)
    | zero => simp
    | add y z _ _ hy hz =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem hy hz
    | smul a y _ hy =>
        obtain ⟨b, hb⟩ := star_algebraMap_ringOfIntegers_mem_range a
        rw [← algebraMap_smul K a y, LinearMap.map_smulₛₗ₂]
        change star (algebraMap (𝓞 K) K a) • hform H y ((d : 𝓞 K) • x) ∈ _
        rw [← hb, algebraMap_smul K]
        exact Submodule.smul_mem _ _ hy
  have hcK : algebraMap (𝓞 K) K c ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (𝓞 K) K).ne hc
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply (Submodule.smul_mem_iff _ hdK).mp
  rw [algebraMap_smul K]
  apply (Submodule.smul_mem_iff _ hcK).mp
  rw [algebraMap_smul K]
  exact Submodule.subset_span (hdual _ hmem)

private theorem full_matLat {K : Type} [Field K] [NumberField K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Function.Surjective A.mulVec)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsFullLattice K M) :
    Submodule.IsFullLattice K (matLat A M) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg K (hM.fg.map _), span_eq_top := ?_ }
  rw [matLat, Submodule.map_coe]
  change Submodule.span K (A.mulVecLin '' (M : Set _)) = ⊤
  rw [Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact hA

private theorem full_Lam {K : Type} [Field K] [NumberField K] [StarRing K]
    {G : Type} [Group G] [Fintype G] {Pl0 : Type} {B : BlockDat K G Pl0}
    {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K}
    (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) :
    Submodule.IsFullLattice K (B.abelian₂ ℓ Z) := by
  have hc : ((Fintype.card G * s : ℕ) : 𝓞 K) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Fintype.card_pos (α := G)) h.good.s_pos).ne'
  have hLat := B.Mt_lat hv0 h hX
  have hMt : Submodule.IsFullLattice K (B.Mt ℓ) :=
    { toIsLattice := hLat
      span_eq_top := span_of_scaled_dual _ _ hLat.fg hc (B.Mt_dual hv0 h hX) }
  exact full_matLat (B.Pq ℓ Z) (B.Pq_surj hv0 h hX) (B.Mt ℓ) hMt

private theorem rr_span_eq_top (P : RowSideFamily ex) {s : ℕ} (hOk : P.A3.fam3.Ok3 s)
    (hF : ColFacts P.S1 P.C) :
    Submodule.span D.what₂.LL (P.S1.RR : Set (Fin P.S1.D → D.what₂.LL)) = ⊤ := by
  let _ : Finite P.T := hOk.ok2.tup_fin
  let _ : Fintype P.T := Fintype.ofFinite P.T
  let side := P.A3.side3 P.Ps P.ψs P.Zs
  let localLat (t : P.T) := matLat (P.S1.ι t) (side.abelian₂ t)
  have hlocal (t : P.T) :
      Submodule.span D.what₂.LL (localLat t : Set (Fin P.S1.D → D.what₂.LL)) = ⊤ := by
    have hL : Submodule.IsFullLattice D.what₂.LL (side.abelian₂ t) :=
      full_Lam (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs)
        hOk.ok2.conj (hOk.ok2.what₂ t) hOk.ok2.irr
    exact (full_matLat (P.S1.ι t) (hF.bij t).2 _ hL).span_eq_top
  rw [eq_top_iff]
  intro x _
  -- A common denominator puts the vector in the local lattice at every prime.
  have hclear (t : P.T) : ∃ d ∈ nonZeroDivisors (𝓞 D.what₂.LL), d • x ∈ localLat t := by
    have hx : x ∈ locS (nonZeroDivisors (𝓞 D.what₂.LL)) (localLat t) := by
      rw [indexBasic_locS_top (K := D.what₂.LL) _ (hlocal t)]
      exact Submodule.mem_top
    exact hx
  choose d hd hdx using hclear
  let r := ∏ t : P.T, d t
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => nonZeroDivisors.ne_zero (hd t)
  have hrK : algebraMap (𝓞 D.what₂.LL) D.what₂.LL r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL).ne hr
  apply (Submodule.smul_mem_iff _ hrK).mp
  rw [algebraMap_smul D.what₂.LL]
  apply Submodule.subset_span
  change r • x ∈ glueLat (fun w => localLat (P.S1.μ w))
  rw [glueLat, Submodule.mem_iInf]
  intro w
  apply locBasic_le_locS _ _
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ (P.S1.μ w))
  rw [show r = d (P.S1.μ w) * a from ha, mul_comm, mul_smul]
  exact (localLat _).smul_mem a (hdx _)

theorem rrFull_of (P : RowSideFamily ex) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) : D.RRFull := by
  have hlat : Submodule.IsLattice D.what₂.LL (P.A3.indefDown P.S1).RR := hF.rr_lattice
  have hspan : Submodule.span D.what₂.LL
      ((P.A3.indefDown P.S1).RR : Set (Fin (P.A3.indefDown P.S1).D → D.what₂.LL)) = ⊤ :=
    rr_span_eq_top P hOk hF
  have hL : D.div.RR.L = (P.A3.indefDown P.S1).RR.map (P.I.eRR.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) :=
    hR.sharpRR.lat
  refine ⟨by rw [hL]; exact hlat.fg.map _, ?_⟩
  have hset : (D.div.RR.L : Set D.div.RR.V) = P.I.eRR.toLinearMap '' ((P.A3.indefDown P.S1).RR : Set _) := by
    rw [hL, Submodule.map_coe]; rfl
  rw [hset, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact P.I.eRR.surjective

theorem buRational_of (P : RowSideFamily ex) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hPt : RowsHoldDcPt3 P)
    (hBu : Rows.BuDefQ D.what₂) : D.BuRational := by
  intro u φ x
  obtain ⟨x', rfl⟩ := (P.I.eNu u).surjective φ
  obtain ⟨y, rfl⟩ := P.I.eRR.surjective x
  rw [hBu, hR.colsBk u x' y]
  have hform := P.tied.div.sharp.forms P.A3.A.μ0
  refine PerDescent.per_sec D u (D.jN u (P.I.eNu u x')) (P.I.tup P.A3.A.μ0) P.tied.div.tup.mu0
    (fun F => P.I.jA P.A3.A.μ0 ((rV0 D P.A3.A P.Ps P.ψs P.A3.A.μ0).mulVec F)) P.I.eRR
    (fun F => (P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F))
    (P.C.B (P.I.wU u) x') ?_ ?_ ?_ ?_ y
  · exact (hF.bij _).2.comp (hF.wf.Pq_surj _)
  · exact range_op_eq_span hform _ (fun z => lvlOp_range _ _ _ _ _ z)
      (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hOk.ok2 P.Ps P.ψs (P.A3.fam3.toSub2 P.Zs) P.A3.A.μ0 F)
  · intro F
    have h := P.tied.div.sharp.iota P.A3.A.μ0 F
    rw [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota] at h
    exact h
  · intro F
    have h1 : P.Dc.Pt (P.I.wU u) P.A3.A.μ0 x' F = P.C.ζ (P.I.wU u) P.A3.A.μ0 * P.C.B (P.I.wU u) x'
        ((P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F)) := hF.l1b.1 _ _ _ _
    have h2 : P.C.ζ (P.I.wU u) P.A3.A.μ0 = 1 := hF.l1b.2.1 _
    rw [h2, one_mul] at h1
    exact (hPt u P.A3.A.μ0 x' F).symm.trans (congrArg D.what₂.embLL h1)

end Formalism.L2.DIV.RatFullPt

end
