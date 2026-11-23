module

public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPfBC
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pos_ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem pos_frMap (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {K₁ K₂ : Type}
    [Field K₁] [Field K₂] [Algebra c.F K₁] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂) (y : FrPt Xo c K₁) :
    ∃ z : FrPt Xo c K₂, FrMap φ y z := by
  classical
  let _ : Algebra K₁ K₂ := φ.toRingHom.toAlgebra
  have htow : ∀ r : c.F, algebraMap c.F K₂ r = algebraMap K₁ K₂ (algebraMap c.F K₁ r) := fun r => (φ.commutes r).symm
  have : FaithfulSMul K₁ K₂ := (faithfulSMul_iff_algebraMap_injective K₁ K₂).2 (algebraMap K₁ K₂).injective
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback y.x).obj Xo.univ.t.G)
  have hco : ∀ τ i, ∃ cc, y.u τ i = gfpVec y.x xc cc := fun τ i => gfp_exists hx _ (y.tan τ i)
  choose d hdu using hco
  have hdW : ∀ τ i, d τ i ∈ gfpEig (c := c) hx τ := fun τ i =>
    (gfp_eig_iff hx τ _).1 (by rw [← hdu τ i]; exact y.eig τ i)
  have hd : ∀ τ, LinearIndependent K₁ (d τ) := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hu : y.u τ = fun i => gfpVec y.x xc (d τ i) := funext (hdu τ)
    have h0 : (0 : Fin n → K₁) ∈ gfpEig (c := c) hx τ := Submodule.zero_mem _
    obtain ⟨a, -, ha⟩ := y.basis τ (gfpVec y.x xc 0) (gfp_tan hx 0) ((gfp_eig_iff hx τ 0).2 h0)
    have e1 : IsCombAt y.x (y.u τ) g (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) g 0).2 hg.symm
    have e2 : IsCombAt y.x (y.u τ) 0 (gfpVec y.x xc 0) := by
      rw [hu]
      exact (gfp_comb_iff hx (d τ) 0 0).2 (by simp)
    have e3 := (ha g e1).trans (ha 0 e2).symm
    exact fun i => congrFun e3 i
  obtain ⟨xc', hx', hv, htm⟩ := gfp_bc (L' := K₂) hx
  have hx0' := gfp_over_bc htow y.x_over
  have hW' : ∀ τ j, (algebraMap K₁ K₂ ∘ d τ j) ∈ gfpEig (c := c) hx' τ := by
    intro τ j
    have h0 := hdW τ j
    unfold gfpEig at h0 ⊢
    rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff] at h0 ⊢
    intro a
    rw [htm a (d τ j), h0 a]
    funext k
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, htow]
  have hli : ∀ τ, LinearIndependent K₂ (fun i => algebraMap K₁ K₂ ∘ d τ i) := fun τ =>
    linearIndependent_algebraMap_comp_iff.mpr (hd τ)
  refine ⟨⟨spMap (algebraMap K₁ K₂) ≫ y.x, hx0', fun τ i => gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i),
    fun τ i => gfp_tan hx' _, fun τ i => (gfp_eig_iff hx' τ _).2 (hW' τ i),
    fun τ w hw he => gfp_basis hx0' hx' τ _ (hli τ) (hW' τ) w hw he,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.secCP (ReciprocityTheory.ChartRestriction.G.PullbackSections.cpS (algebraMap K₁ K₂) y.x) y.s,
    fun s' => ReciprocityTheory.ChartRestriction.G.PullbackSections.genBC_frame y.x hS hT (algebraMap K₁ K₂) y.s y.gen s'⟩, rfl, fun τ i => ?_,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm (algebraMap K₁ K₂) y.x, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_snd _ _, ReciprocityTheory.ChartRestriction.G.PullbackSections.bcPm_fst _ _,
    fun i h => rfl⟩
  show gfpVec _ xc' (algebraMap K₁ K₂ ∘ d τ i) = spMap (dualMap φ.toRingHom) ≫ y.u τ i
  rw [hdu τ i]
  exact hv (d τ i)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem wchar_nsmul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) (k : ℕ) :
    wchar (k • e) t = wchar e t ^ k := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem wchar_ne_zero {S : Type} [Field S] (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) : wchar e t ≠ 0 := by
  unfold wchar
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero

end Weights

variable {D : D7} {T : Top D}

theorem exponent_base_weight_zero (j : ℕ) : ex (T.Q.Dw j) (wtA (wt0 D j)) (wt0 D j).n = 0 := by
  funext i
  cases i <;> simp [ex, wtA, wt0, wscalar, ext0]

theorem ex_addL {j : ℕ} (wL : WeightFamilies.Wt D j) (k : ℕ) :
    ex (T.Q.Dw j) (wtA (addL (wt0 D j) wL k)) (addL (wt0 D j) wL k).n = k • ex (T.Q.Dw j) (wtA wL) wL.n := by
  induction k with
  | zero => rw [addL_zero, exponent_base_weight_zero, zero_smul]
  | succ k ih => rw [← wadd_addL, wtA_wadd, n_wadd, ex_add, ih, succ_nsmul, add_comm]

variable (j : ℕ)

def evIHom {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) : T.R j →+* Tc.Fr where
  toFun := evI y
  map_one' := by
    letI := io.toAlgebra
    exact evalAt_one _ _ y.1 y.2.1
  map_mul' := evI_mul y
  map_zero' := by
    letI := io.toAlgebra
    exact evalAt_zero _ _ y.1
  map_add' := evI_add y

def chiI {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) :
    AddMonoidAlgebra (T.R j) (Deg D j) →+* Tc.Fr :=
  AddMonoidAlgebra.liftNCRingHom (evIHom j y) (1 : Multiplicative (Deg D j) →* Tc.Fr) (fun _ _ => Commute.all _ _)

theorem chiI_single {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (d : Deg D j) (r : T.R j) :
    chiI j y (AddMonoidAlgebra.single d r) = evI y r := by
  unfold chiI
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [MonoidHom.one_apply, mul_one]
  rfl

theorem chiI_smul {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (a : T.Q.c.F)
    (f : AddMonoidAlgebra (T.R j) (Deg D j)) : chiI j y (a • f) = io a * chiI j y f := by
  refine AddMonoidAlgebra.induction_linear f ?_ ?_ ?_
  · rw [smul_zero, map_zero, mul_zero]
  · intro f g hf hg
    rw [smul_add, map_add (f := _), map_add (f := _), hf, hg, mul_add]
  · intro d r
    rw [show a • AddMonoidAlgebra.single d r = AddMonoidAlgebra.single d (a • r) from AddMonoidAlgebra.smul_single a d r,
      chiI_single, chiI_single, evI_smul]

theorem chiI_inc (h : LawsP T) {Tc : CDVR} {io : T.Q.c.F →+* Tc.Fr} (y : IntFr (T.Q.Xo j) T.Q.c Tc io) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : chiI j y (incG deg (cutR T.C j) w F) = evI y (F : T.R j) := by
  rw [incG_apply, chiI_single]

section Main

variable {D : D7} {T : Top D}

theorem evR_eq_of_map {j : ℕ}
    (hWD : EvalWD (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z))
    {f : T.R j} (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (w : FrPt (T.Q.Xo j) T.Q.c S) (p : TRing T.Q.c.F)
    (φ : p.R →ₐ[T.Q.c.F] S) (y : FrPt (T.Q.Xo j) T.Q.c p.R) (h : FrMap φ y w) :
    evR (T.Q.Xo j) T.Q.c f w = φ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact hWD f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec h

def RealPtNZSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : (extAll h j hj).Pt' la) (Tc : CDVR) (ι : Loc ζ →+* Tc.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (recPlus h j hj) la G.N →+* Tc.Fr)
    (hu : IsUnit (ev (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) =
      nval Tc.V (ep (unifO (recPlus h j hj) la G.N) ζ) (ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)))) ∧
    (∀ x : ↥(Frac0 (recPlus h j hj) la G.w),
      IsLocalization.Away.lift (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec (recPlus h j hj) la G.w 0) hu (x : Lw (recPlus h j hj) la G.w) =
        phiAt ζ Tc.Fr ι hU (addVal_map_of_unr ι hunr) (toOsK (recPlus h j hj) la G.w x)) ∧
    ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
      ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0

end Main

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SupPTGePf
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def SupPtAt (σ : Tc.Q.c.F →+* ℂ) : Type :=
  Σ k : (Tc.U j σ).Comp, {x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((Tc.U j σ).X k).Ψ D.R.r // x ∈ ((Tc.U j σ).X k).dom}


def DensK (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c) (ka : WeightFamilies.Wt D j)
    (pt : ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (P : Om Z →+* ℂ), SupPtAt j (goodOf Tc.Q.c (sgOf P))) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, recNrm (Tc.U j (goodOf Tc.Q.c (sgOf (P : Om Z →+* ℂ)))) (xiR D) (wtA ka) ka.n
          (F : Tc.R j) (pt Z P).1 (pt Z P).2.1

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdR {u : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j u) :=
  rdU (T.U j T.σ₀) F.1

def TieReadSt : Prop :=
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp),
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) ∧
  ∀ u : WeightFamilies.Wt D j, ReciprocityTheory.ChartRestriction.G.PullbackSections.JInjRd T j (wtA u) u.n

abbrev KT (T : Top D) (j N : ℕ) : Type := FractionRing (MvPolynomial (Idx D j N) T.Q.c.F)

def TieMaxCuspSt (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ F : (recB h.toLawsCore).Cusp j ka,
    F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka ↔
      ∀ k, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt c j)

end Formalism.L2.Pj
end
end

