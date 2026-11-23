module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
public import Formalism.LocalToGlobal.Divisibility.MemberDIV
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.ArithClauseRec
section
noncomputable section

namespace Formalism.L2.DIV.Arith4S

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open NumberField IsDedekindDomain

def c0F (Ch Cc CYL Ct : ℝ) : ℝ := max 28 (max (2 * (1 + |Cc|) + 1) (max 1 (Ch * (3 + 2 * CYL + (max Ct 5 + 3)))))

def ceF (C Ce cD C0 : ℝ) : ℝ := max C0 (C + 2 + C + (Ce + cD) + 1)

def x0F (eps Ct Cc CH ce : ℝ) : ℝ :=
  max (max 16 ((48 * (max Ct 5 + 3) / eps + 6 / eps + 2) ^ (6 / eps)))
    (max (3 + |Cc|) (max (max 9 (272 + 2 * ce))
      (max (⌈(9 * (max Ct 5 + 3) + 1 + 1) / eps⌉₊.factorial : ℝ) (⌈(max CH 0 + 1) / eps⌉₊.factorial : ℝ))))

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

theorem arithClause_rec (hS : SizesAt L) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (P5 : ParameterChoice' D L) (hFD : L.FDef) (hK : DV.KapDef D)
    {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T D.R.m)
    (hc : Fintype.card G = D.what₂.restRowsFiniteGroupCard) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (cf : ConvFace A3.fam3.base3) (C CH Ch Ce cD : ℝ)
    (hTf : Finite T) (hDG : DGamSize A3.A P0 ψ0 (ofRecord D L Del h0) L.Nc hTf 1 cD)
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch)
    (hx : x0F L.sc.eps L.Ct L.Cc CH (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) ≤ L.sc.x) :
    ∀ Pk : IndefPkgR A3.fam3.amb3
        (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) (Equiv.refl _) L.Nc Ch)) cf C CH,
    ∃ (lam0 Sw C1 : ℝ) (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0
        (c0F Ch L.Cc P5.CYL L.Ct) (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) Ch Sw C1) (dg : ℕ),
      0 < dg ∧ (∀ j t, (A3.A.fam.L j t).DG (A3.A.fam.lvlA P0 ψ0) ∣ dg) ∧
      ∀ u, ArithAt A3 1 P0 ψ0 P1 ψ1 Dc Sp (ZscFix3 A3 P0 ψ0 (ofRecord D L Del h0) (Equiv.refl _) L.Nc Ch) cf C CH Pk
        (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0
          (c0F Ch L.Cc P5.CYL L.Ct) (ceF C Ce cD (c0F Ch L.Cc P5.CYL L.Ct)) Ch Sw C1 (H u))
        (fun _ => divSize L Ce) dg := by
  intro Pk
  set C0 := c0F Ch L.Cc P5.CYL L.Ct with hC0def
  set ce := ceF C Ce cD C0 with hcedef
  have h28 : 28 ≤ C0 := le_max_left _ _
  have hC1 : constantOneChoice L + 1 ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hC0 : max 1 (Ch * (3 + 2 * P5.CYL + (max L.Ct 5 + 3))) ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
  have hce0 : C0 ≤ ce := le_max_left _ _
  have hce : C + 2 + C + (Ce + cD) + 1 ≤ ce := le_max_right _ _
  have hxB : max 16 ((48 * (max L.Ct 5 + 3) / L.sc.eps + 6 / L.sc.eps + 2) ^ (6 / L.sc.eps)) ≤ L.sc.x :=
    (le_max_left _ _).trans hx
  have hrest := (le_max_right _ _).trans hx
  have hx3 : 3 + |L.Cc| ≤ L.sc.x := (le_max_left _ _).trans hrest
  have hrest2 := (le_max_right _ _).trans hrest
  have hxq : max 9 (272 + 2 * ce) ≤ L.sc.x := (le_max_left _ _).trans hrest2
  have hrest3 := (le_max_right _ _).trans hrest2
  have hx1 : (⌈(9 * (max L.Ct 5 + 3) + 1 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x := (le_max_left _ _).trans hrest3
  have hx2 : (⌈(max CH 0 + 1) / L.sc.eps⌉₊.factorial : ℝ) ≤ L.sc.x := (le_max_right _ _).trans hrest3
  have hB : BigX L := bigX_of L ((le_max_left _ _).trans hxB) ((le_max_right _ _).trans hxB)
  refine ⟨Real.log (Fintype.card G), swRec L, constantOneChoice L,
    fun u => numFacts_rec L Del h0 hS hB hDel hh0 P5 u hx3 ((le_max_left _ _).trans hxq) G hc C0 ce Ch hCh hC0 hC1 hce0,
    dgOf A3.A P0 ψ0 hTf, dgOf_pos A3.A P0 ψ0 hTf, dgOf_dvd A3.A P0 ψ0 hTf, fun u => ?_⟩
  exact arithAt_rec L Del h0 hS hB hDel hh0 P5 hFD hK u hx3 A3 hc P0 ψ0 P1 ψ1 Dc Sp (Equiv.refl _) cf C CH Ch C0 ce Ce Pk
    (dgOf A3.A P0 ψ0 hTf) cD hDG hC hCh h28 hC1 hC0 hce0 hce hxq hx1 hx2

end Formalism.L2.DIV.Arith4S

end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.TupUsed
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.DIV

open Formalism.L2.Rows Formalism.L2.Indef

section IndefiniteRowSideFullHecke

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def TupAllUsed (P : RowSideFamily ex) : Prop := ∀ t : P.T, Formalism.IndefR.RecTie.Used0 D (P.I.tup t)

theorem tupAllUsed_of_cover (P : RowSideFamily ex)
    (h : ∀ t : P.T, t = P.A3.A.μ0 ∨ ∃ w, t = (P.A3.indefDown P.S0).μ (D.plEq w)) : TupAllUsed P := by
  have hT : TupTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup := by
    exact P.tied.div.tup
  intro t
  rcases h t with rfl | ⟨w, rfl⟩
  · exact Or.inl hT.mu0
  · exact Or.inr ⟨w, (hT.muAt w).symm⟩

def LiftInvariantSpan (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def RationalLiftSpanAtUsedTuples (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def ThTheta (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T) x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def ThThetaG (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def DcPtG (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

variable {P : RowSideFamily ex}

theorem lift_invariant_span_used_of (h : LiftInvariantSpan P) : RationalLiftSpanAtUsedTuples P := fun i t _ => h i t

theorem lift_invariant_span_of_used (hU : TupAllUsed P) (h : RationalLiftSpanAtUsedTuples P) : LiftInvariantSpan P := fun i t => h i t (hU t)

theorem thThetaG_of (h : ThTheta P) : ThThetaG P := fun i t _ x => h i t x

theorem thTheta_of_G (hU : TupAllUsed P) (h : ThThetaG P) : ThTheta P := fun i t x => h i t (hU t) x

theorem dcPtG_of (h : RowsHoldDcPt3 P) : DcPtG P := fun u t _ x F => h u t x F

theorem dcPt_of_G (hU : TupAllUsed P) (h : DcPtG P) : RowsHoldDcPt3 P := fun u t x F => h u t (hU t) x F


open Classical in
structure NumTieG (P : RowSideFamily ex) : Prop where

  Ij : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.Ij (P.I.tup t) ((i : ℕ) + 1) w = (P.A3.indefDown P.S0).Iw i t (D.plEq w)

  jw : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.jw (P.I.tup t) ((i : ℕ) + 1) w =
      Formalism.DivisionValues.jw ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).HT i t) (D.plEq w)
        ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).Tl i t)

  etaJ : ∀ (i : Fin D.R.m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ (P.A3.indefDown P.S0).Tw then
      P.A3.A.fam.etaJ P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i ((P.A3.indefDown P.S0).μ (D.plEq w)) (D.plEq w) else 0

theorem numTieG_of (h : NumTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup) : NumTieG P := ⟨fun i t _ w => h.Ij i t w, fun i t _ w => h.jw i t w, h.etaJ⟩

theorem numTie_of_G (hU : TupAllUsed P) (h : NumTieG P) : NumTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup := ⟨fun i t w => h.Ij i t (hU t) w, fun i t w => h.jw i t (hU t) w, h.etaJ⟩

structure DivRows3G (P : RowSideFamily ex) : Prop where

  sharpRR : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR

  baseRR : HLatTie ex.p0.s.RR (P.A3.indefDown P.S0).RR (P.A3.indefDown P.S0).XE P.I.eRR0

  divisionRows_rationalLift : RationalLiftSpanAtUsedTuples P

  thTheta : ThThetaG P

  num : NumTieG P

  colsBk : ∀ u x y, D.div.Bk u (P.I.eNu u x) (P.I.eRR y) =
    (P.A3.colData2 P.C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)).B (P.I.wU u) x y

theorem DivRows3.toG (h : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) : DivRows3G P :=
  { sharpRR := h.sharpRR
    baseRR := h.baseRR
    divisionRows_rationalLift := lift_invariant_span_used_of h.divisionRows_rationalLift
    thTheta := thThetaG_of h.thTheta
    num := numTieG_of h.num
    colsBk := h.colsBk }

theorem DivRows3G.toRows (hU : TupAllUsed P) (h : DivRows3G P) :
    DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I :=
  { sharpRR := h.sharpRR
    baseRR := h.baseRR
    divisionRows_rationalLift := lift_invariant_span_of_used hU h.divisionRows_rationalLift
    thTheta := thTheta_of_G hU h.thTheta
    num := numTie_of_G hU h.num
    colsBk := h.colsBk }

end IndefiniteRowSideFullHecke

section Member

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.BasicNotions.DV Formalism.L2.Col Formalism.L2.DIV.Member

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  {F : ColFam W Ch sel Sg Gc m2 D.what₂.Word} {hX : (fieldsLL D X e).Ok}
  {v0 : InfinitePlace D.what₂.LL} {TU : Finset (Tup X.F X.E D.what₂.LL Sg)}
  {Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL)}
  {xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ}
  {trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL}
  {hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok}
  {ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch)}
  {Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs)}

end Member

end Formalism.L2.DIV
end
end

