module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T)

theorem combAlg_of_combBound (j : ℕ) (hj : InR D j) (hjm : j < D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (cb / (2 * (G.iet : ℝ))) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := y0.2
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz
  let y : T.PtA j la := PtV.mk la ho z hz η hη
  have hyv : vAtV y = vAtV y0 := funext fun g => by
    show y.1.1 g = y0.1.1 g
    rw [hq]
    rfl
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hyv]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  obtain ⟨h0, h1⟩ := (hX la y).1 hjm
  rw [hv] at h0 h1
  rw [hd] at h1
  refine ⟨h0, fun htop => ?_⟩
  have h2 := h1 htop
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)] at h2
  exact h2

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FullExists
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Full (D : D7) : Type 1 extends Top D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

variable {D : D7}

def Full.J (T : Full D) : CoreJ D :=
  { toCore := T.toTop.toCore, cE := T.cE, chiW := T.chiW, x₀ := T.x₀, iota := T.iota }

def Full.XiVal (T : Full D) (j n : ℕ) : Prop :=
  ∃ (hr : (T.V j T.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (T.V j T.σ₀) hr T.σ₀ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j T.σ₀) fun _ => T.xi

structure LawsFull (T : Full D) : Prop where
  p : LawsP T.toTop
  j : LawsJ T.J
  sh : LawsSh T.toTop

  canon : T.Q.Canon

  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1

  halfI : ∀ j, InR D j → ∀ n, (T.dδ j n).I = T.half₂

  shUniq : ∀ j, InR D j → ∀ n (_ : StarRing (𝓞 D.host.E)) (nab' : NabV (T.dδ j n).Xo₂ (T.dδ j n).c₂),
    IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ nab' → ∀ a, Dom a n →
      shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n { T.dδ j n with nab₂ := nab' } =
        shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)

  xiVal : ∀ j, InR D j → ∀ n, T.XiVal j n

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def extAll : PtExt (recPJ h j hj) where
  Pt' la := valSet (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) la
  extendedPointBaseChange la _ := (T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).yEta
    (Classical.choice ((T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).genNe _))
  vAt' _ y := vG y.1
  vAt'_zero la y := vG_zero (isVal_valSet la y.1 y.2).zero
  vAt'_ne_bot la y := vG_ne_bot (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).ne_bot
  vAt'_add la y := vG_add (isVal_valSet la y.1 y.2).add
  vAt'_smul la y a F ha := vG_smul (fun r => (isVal_valSet la y.1 y.2).smul a r ha) F
  vAt'_mul la y := vG_mul deg (cutR T.C j) (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).mul

theorem extAll_vAt_inc (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (extAll h j hj).Pt' la) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 := by

  have hinc : ∀ m, ((recPJ h j hj).inc w F).coeff m = if deg w = m then F.1 else 0 := by
    intro m
    show (AddMonoidAlgebra.single (deg w) _).coeff m = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have h0 : y.1 0 = ⊤ := by
    first
      | exact (isVal_valSet la y.1 y.2).zero
      | simpa using (isVal_valSet la y.1 y.2).zero
  show vG y.1 ((recPJ h j hj).inc w F) = y.1 F.1
  unfold vG
  simp only [hinc]
  apply le_antisymm
  · exact iInf_le_of_le (deg w) (by simp)
  · refine le_iInf fun m => ?_
    split_ifs with hm
    · exact le_rfl
    · rw [h0]
      exact le_top

theorem intAtExt_extAll : IntAtExt _ (extAll h j hj) := by
  intro w F hF la y
  rw [extAll_vAt_inc]
  exact (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) hF la y.1 y.2

def recPlus : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j := xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftInSt
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def LocRingSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hw : ∀ ζ, FromW ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (∃ (k : ℕ) (p q : Rp (xplus X E hM) la G.N),
      p ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧ q ∈ Vw (xplus X E hM) la G.N (addL (wt0 D j) wL k) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β p = 0) ∧
      (∀ β, β ≠ 0 → hasseRp (xplus X E hM) la G.N β q = 0) ∧
      ∀ ζ, (hw ζ).ev p ≠ 0 ∧ (hw ζ).ev q ≠ 0 ∧
        vV (hw ζ).T.V ((hw ζ).ev p) + vV (hw ζ).T.V ((hw ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0))) =
          vV (hw ζ).T.V ((hw ζ).ev q)) ∧
    ∀ g : ↥(Frac0 (xplus X E hM) la G.w),
      (∀ ζ, 0 ≤ nval (hw ζ).T.V 1 ((hw ζ).toSecPt.lift (g : Lw (xplus X E hM) la G.w))) →
      ∃ (f d : ↥(Frac0 (xplus X E hM) la G.w)) (hd : ∀ ζ, (hw ζ).toSecPt.lift (d : Lw (xplus X E hM) la G.w) ≠ 0),
        toOsK (xplus X E hM) la G.w f = toOsK (xplus X E hM) la G.w d * toOsK (xplus X E hM) la G.w g ∧
        ∀ (l : List (Idx D j G.N →₀ ℕ)) (ζ : PtsG G la),
          0 ≤ nval (hw ζ).T.V 1 (evL (fun ζ => (hw ζ).toSecPt) ζ (hdList (fun ζ => (hw ζ).toSecPt) l
            (ιW (fun ζ => (hw ζ).toSecPt) (f : Lw (xplus X E hM) la G.w) *
              ↑(isUnit_of_lift_ne (fun ζ => (hw ζ).toSecPt) hd).unit⁻¹)))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftUnit
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

theorem isUnit_toOsK_of_lift {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ)) (C : CurveModel G la g0)
    (x : ↥(Frac0 (xplus X E hM) la G.w))
    (hx : ∀ ζ, (hw ζ).toSecPt.lift (x : Lw (xplus X E hM) la G.w) ≠ 0) :
    IsUnit (toOsK (xplus X E hM) la G.w x) := by
  classical
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
    exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv
  have : IsReduced (OsK (xplus X E hM) la G.w) := by
    have : IsReduced (↥C.A' ⧸ C.JA) := C.red
    exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective
  have : IsArtinianRing (OsK (xplus X E hM) la G.w) := IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _
  by_contra hnu
  set a := toOsK (xplus X E hM) la G.w x with ha
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum (OsK (xplus X E hM) la G.w), a ∈ I.asIdeal := by
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact ⟨⟨M, hM⟩, haM (Ideal.subset_span rfl)⟩
  let e := IsArtinianRing.equivPi (OsK (xplus X E hM) la G.w)
  set ε := e.symm (Pi.single I 1) with hε
  have hεa : ε * a = 0 := by
    apply e.injective
    rw [map_mul, map_zero, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm
      rw [Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]
      show Ideal.Quotient.mk m.asIdeal a = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hI
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul, Pi.zero_apply]
  have hεε : ε * ε = ε := by
    apply e.injective
    rw [map_mul, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm; rw [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul]
  have hε0 : ε ≠ 0 := by
    intro h
    have h1 := congrArg e h
    rw [hε, e.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 I
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    have h3 : (1 : OsK (xplus X E hM) la G.w) ∈ I.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h2)
    exact I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hint : IsIntegral (Op (xplus X E hM) la G.N) ε := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [pow_two, hεε]
  let ε' : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ⟨ε, hint⟩
  have hnot : ¬ IsUnit (1 - ε') := by
    intro hu
    apply hε0
    have h1 : ε' * (1 - ε') = 0 := by
      apply Subtype.ext
      show ε * (1 - ε) = 0
      rw [mul_sub, mul_one, hεε, sub_self]
    have h2 := (hu.mul_left_eq_zero).1 h1
    exact congrArg Subtype.val h2
  obtain ⟨Z, hZ, hZ1⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ε'}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  let ζ : PtsG G la := ⟨Z, hZ⟩
  have hεZ : ε' ∉ ζ.asIdeal := by
    intro h
    have h1 : (1 - ε') + ε' ∈ Z := Z.add_mem (hZ1 (Ideal.subset_span rfl)) h
    rw [sub_add_cancel] at h1
    exact hZ.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨e0, he0⟩ := toOsK_surjective (xplus X E hM) la G.w ε
  have hev := (hw ζ).evW e0 ε' he0
  have hu : IsUnit (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) ε') :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal ε').2 hεZ
  have hne : (hw ζ).toSecPt.lift (e0 : Lw (xplus X E hM) la G.w) ≠ 0 := by
    rw [hev]
    exact ((hu.map (hw ζ).ι).map (algebraMap (hw ζ).T.V (hw ζ).T.Fr)).ne_zero
  have hJ : e0 * x ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_mul, he0]
    exact hεa
  have h0 := (hw ζ).toSecPt.lift_Jid hJ
  rw [Subalgebra.coe_mul, map_mul] at h0
  exact mul_ne_zero hne (hx ζ) h0

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

theorem prodInLat_of (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hka : ∀ x, wtA ka x = n * wtA wL x) (hkn : ka.n = n * wL.n) : ProdInLat hL j ka wR n := by
  have hV : ∀ la, ∀ v ∈ Tc.Vs j la, IsVal la v := fun la => isVal_valSet la
  have hw1 : ∀ k, wR k ∈ Tc.C j wL ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (wR k) := by
    intro k
    obtain ⟨F, hF, hFk⟩ := hw k
    rw [← hFk]
    exact ⟨cutR_le Tc.C j wL F.2, hF⟩
  have key : ∀ m (s : Fin (m + 1) → Fin (N + 1)), ∃ W : WeightFamilies.Wt D j, (∀ x, wtA W x = (m + 1) * wtA wL x) ∧
      W.n = (m + 1) * wL.n ∧ ∏ k, wR (s k) ∈ Tc.C j W ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (∏ k, wR (s k)) := by
    intro m
    induction m with
    | zero =>
      intro s
      refine ⟨wL, fun x => by ring, by ring, ?_, ?_⟩
      · rw [Fin.prod_univ_one]; exact (hw1 _).1
      · rw [Fin.prod_univ_one]; exact (hw1 _).2
    | succ m ih =>
      intro s
      obtain ⟨W, hW1, hW2, hWm, hWv⟩ := ih (fun k => s k.succ)
      refine ⟨WeightAlgebra.wadd wL W, fun x => ?_, ?_, ?_, ?_⟩
      · rw [wtA_wadd, Pi.add_apply, hW1 x]; ring
      · rw [n_wadd, hW2]; ring
      · rw [Fin.prod_univ_succ]; exact hL.mul j hj wL W _ (hw1 _).1 _ hWm
      · intro la v hv
        rw [Fin.prod_univ_succ, (hV la v hv).mul]
        exact add_nonneg ((hw1 _).2 la v hv) (hWv la v hv)
  intro s
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W, hW1, hW2, hWm, hWv⟩ := key m s
  have hmem : ∏ k, wR (s k) ∈ Tc.C j ka := by
    have hC : Tc.C j ka = Tc.C j W := by
      show Tc.cuspA j (wtA ka) ka.n = Tc.cuspA j (wtA W) W.n
      rw [hkn, hW2, show wtA ka = wtA W from funext fun x => by rw [hka x, hW1 x]]
    rw [hC]; exact hWm
  refine ⟨⟨∏ k, wR (s k), ?_⟩, ?_, rfl⟩
  · show _ ∈ cutR Tc.C j ka
    rw [cutR_eq Tc.C hj]; exact hmem
  · exact hWv

theorem prodInLat_of_wtZ (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hkaZ : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) : ProdInLat hL j ka wR n := by
  refine prodInLat_of hL j hj wR wL ka n hw hn (fun x => ?_) ?_
  · have h1 := congrFun (congrArg Prod.fst hkaZ) x
    simp only [wtZ, Prod.smul_fst, Pi.smul_apply] at h1
    rw [nsmul_eq_mul] at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd hkaZ
    simp only [wtZ, Prod.smul_snd] at h2
    rw [nsmul_eq_mul] at h2
    exact_mod_cast h2

end Formalism.L2.Pj
end
end

