module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0039
public import Development.EtaleCohomology.EtaleSheaves.Bundle0037
public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0036

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleThird
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceDegeneracyIdentities

theorem pull_pull {E : Spc} {U : Scheme.{0}} {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (x : Sx E c U) :
    (E.map f.op).app (op U) ((E.map g.op).app (op U) x) = (E.map (f ≫ g).op).app (op U) x := by
  rw [op_comp, E.map_comp]; rfl

theorem pull_congr {E : Spc} {U : Scheme.{0}} {a b : ℕ} {f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b}
    (h : f = g) (x : Sx E b U) : (E.map f.op).app (op U) x = (E.map g.op).app (op U) x := by rw [h]

theorem f0s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 0 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem L_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (y : Sx E n U) : (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map f.op).app (op U) y) =
      ((ofCat (glCat 1)).map f.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) y) := by
  have h := L.naturality f.op
  have h2 := NatTrans.congr_app h (op U)
  first
  | exact (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h2 y)
  | exact (by simpa only [NatTrans.comp_app, types_comp_apply] using congr_fun h2 y)

theorem line_mul {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 2 U) :
    lineUnit L (y.face 1) = lineUnit L (y.sub 0 1 (by omega)) * lineUnit L (y.sub 1 1 (by omega)) := by
  unfold lineUnit Sx.face Sx.sub SimplicialObject.δ
  rw [L_nat, L_nat, L_nat]
  generalize (L.app (op (SimplexCategory.mk 2))).app (op U) y = z
  let z' : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := z
  change Matrix.GeneralLinearGroup.det (z'.map' 0 2) = Matrix.GeneralLinearGroup.det (z'.map' 0 1) * Matrix.GeneralLinearGroup.det (z'.map' 1 2)
  rw [z'.map'_comp 0 1 2, SingleObj.comp_as_mul, map_mul, mul_comm]

theorem f0s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 0 1 (by omega) = (x.face 3).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 1 1 (by omega) = (x.face 0).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 1 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem local_zero (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hC : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α) {V : Scheme.{0}}
    (x : Sx E 3 V) (a b c : (Γ(V, ⊤))ˣ) (ha : a ^ q = lineUnit L (x.sub 0 1 (by omega)))
    (hb : b ^ q = lineUnit L (x.sub 1 1 (by omega))) (hc : c ^ q = lineUnit L (x.sub 2 1 (by omega))) :
    ev (δ 2 3 α) 3 0 (by simp) V x = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
    2 (-1) 0 (by norm_num) (by norm_num) x
  refine hd.trans ?_
  have h0 : ev α 3 (-1) (by norm_num) V x = 0 :=
    LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q (-1) (by norm_num)) V _ _
  have v0 := hC.2.2 V (x.face 0) b c (by rw [f0s0]; exact hb) (by rw [f0s1]; exact hc)
  have v1 := hC.2.2 V (x.face 1) (a * b) c (by rw [f1s0, line_mul, f3s0, f3s1, mul_pow, ha, hb]) (by rw [f1s1]; exact hc)
  have v2 := hC.2.2 V (x.face 2) a (b * c) (by rw [f2s0]; exact ha) (by rw [f2s1, line_mul, f0s0, f0s1, mul_pow, hb, hc])
  have v3 := hC.2.2 V (x.face 3) a b (by rw [f3s0]; exact ha) (by rw [f3s1]; exact hb)
  rw [Fin.sum_univ_four]
  erw [h0, v0, v1, v2, v3]
  rw [mul_assoc]
  simp only [Sec.map, map_zero, zero_add]
  convert smul_zero (Int.negOnePow 3) using 2
  simp
  abel


open LateralTheory.EtaleFoundations.FirstChernUniqueness in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra := by
  intro q _ E L hi α hC U x
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine loc_imp (loc_and (root_line hr q L hi U (x.sub 0 1 (by omega)))
    (loc_and (root_line hr q L hi U (x.sub 1 1 (by omega))) (root_line hr q L hi U (x.sub 2 1 (by omega)))))
    fun V g hv => ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hv
  rw [← sub_res] at ha hb hc
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, local_zero q L α hC (x.res g) a b c ha hb hc]
  simp [Sec.res]

end LateralTheory.E.ChernCocycleFaceDegeneracyIdentities
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CorePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.CorePf

theorem inf_nonempty {X : Type} [TopologicalSpace X] [PreirreducibleSpace X] {n : ℕ}
    (U : Fin n → TopologicalSpace.Opens X) (hU : ∀ j, (U j : Set X).Nonempty) :
    ∀ s : Finset (Fin n), s.Nonempty → ((s.inf U : TopologicalSpace.Opens X) : Set X).Nonempty := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hU a
  | cons a s ha hs ih =>
    rw [Finset.inf_cons, TopologicalSpace.Opens.coe_inf]
    exact nonempty_preirreducible_inter (U a).2 (s.inf U).2 (hU a) ih

end LateralTheory.E.CorePf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverExistence
section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.CoverExistence

theorem Cover_of : LateralTheory.E.ChowGraphCut.Cover := by
  intro A _ X p _ _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨t.card, fun j => V (t.equivFin.symm j), fun j => hV _, fun j => ⟨_, hxV _⟩, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end LateralTheory.E.CoverExistence
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGeoVCut

namespace LateralTheory.E.LeafGeoVV2Cut

def CurveThroughGenericPointSpreadsToSmoothProperFamily : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

def LeafDescendQF : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) → genericPoint X ∈ Set.range e →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2)
      (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
      IsSeparated q ∧ QuasiCompact q ∧ SmoothOfRelativeDimension 1 q ∧
      IsSeparated (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsSeparated (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      IsIntegral D0 ∧ IsIntegral D1 ∧ IsIntegral D2 ∧
      LocallyQuasiFinite (pullback.lift q f hf.symm) ∧ LocallyQuasiFinite d1 ∧ LocallyQuasiFinite d2 ∧
      topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafExtendZMT : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p]
  (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b]
  (ι : Sp R ⟶ B) [IsOpenImmersion ι], ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k R)) →
  ∀ {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) (e : C0 ⟶ X),
    IsCurve c0 → IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
  ∀ {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X) (v0 : C0 ⟶ D0)
    (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    IsSeparated q → QuasiCompact q → SmoothOfRelativeDimension 1 q →
    IsSeparated (d1 ≫ q) → QuasiCompact (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsSeparated (d2 ≫ d1 ≫ q) → QuasiCompact (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    IsIntegral D0 → IsIntegral D1 → IsIntegral D2 →
    LocallyQuasiFinite (pullback.lift q f hf.symm) → LocallyQuasiFinite d1 → LocallyQuasiFinite d2 →
    IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) →
    γ1 ≫ v0 = v1 ≫ d1 → γ2 ≫ v1 = v2 ≫ d2 → v0 ≫ f = e →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X) (V : B.Opens)
      (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ⊆ V ∧
      SmP π V ∧ SmP (g1 ≫ π) V ∧ SmP (g2 ≫ g1 ≫ π) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback u0 c0 π (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u1 (γ1 ≫ c0) (g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) ∧
      γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

theorem spread_of (hD : LeafDescendQF) (hB : LateralTheory.E.LeafSpreadVCut.LeafCloseB) (hE : LeafExtendZMT) :
    CurveThroughGenericPointSpreadsToSmoothProperFamily := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, hf, sp0, qc0, sm0, sp1, qc1, sm1, sp2, qc2, sm2, i0, i1, i2,
    qf0, qf1, qf2, dD, P0, P1, P2, c1, c2, ve⟩ := hD k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, V, u0, u1, u2, hs, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, ue⟩ :=
    hE k p Ω R B b ι hι c0 γ1 γ2 e hc0 h1 h2 he q d1 d2 f v0 v1 v2 hf sp0 qc0 sm0 sp1 qc1 sm1 sp2 qc2 sm2 i0 i1 i2
      qf0 qf1 qf2 P0 P1 P2 c1 c2 ve
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := LateralTheory.E.LeafSpreadVCut.succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨u0 x, ?_⟩, Q0, Q1, Q2, e1, e2, ue⟩
  show π (u0 x) ∈ (V : Set B)
  rw [← Scheme.Hom.comp_apply, Q0.w]
  exact hs ⟨c0 x, rfl⟩

theorem geoV_of (hC : LeafCurveV) (hS : CurveThroughGenericPointSpreadsToSmoothProperFamily) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he hη C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

end LateralTheory.E.LeafGeoVV2Cut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescentPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.DescentPf

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem val_smul {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (c : ZMod q) (x : Sec (tw q i) U) :
    c.val • x = (ULift.up c : ULift.{1} (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

theorem Descent_of (hAC : LateralTheory.E.LCBijPf.TwGenNZAC) : LateralTheory.E.LCSurjPf.Descent := by
  intro q _ i m hm B _ ζ y hloc
  obtain ⟨S, hS, hP⟩ := hloc
  have hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q),
      Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) →
      Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom) := by
    intro V W g h c hc
    have hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x := fun x => map_nsmul _ _ x
    rw [res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]
    rfl
  have huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B))
      (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) →
      Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) →
      ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2 := by
    intro V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v1 v2 hv
    let A := (pullback g1 g2).affineOpenCover
    obtain ⟨w, -⟩ := A.covers z
    let a := A.f (A.idx z)
    have e1 := hform g1 (a ≫ pullback.fst g1 g2) c1 h1
    have e2 := hform g2 (a ≫ pullback.snd g1 g2) c2 h2
    have hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1 := by
      simp [pullback.condition]
    rw [hcomp] at e2
    have hne : Nontrivial (A.X (A.idx z)) := PrimeSpectrum.nontrivial w
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)
    have key := LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)
    refine sub_eq_zero.1 (key ?_)
    have e := e1.symm.trans e2
    rw [← hφ] at e
    rw [LateralTheory.E.LCBijPf.gam_map]
    rw [val_smul, val_smul] at e
    have hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2 := rfl
    rw [val_smul, hup, sub_smul, sub_eq_zero]
    exact e
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)),
      Etale g ∧ S.arrows g ∧ x ∈ Set.range g := by
    intro x
    obtain ⟨j, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let A := (𝒰.X j).affineOpenCover
    obtain ⟨w, hw⟩ := A.covers v
    have : Etale (𝒰.f j) := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j
    refine ⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hw, hv]
  choose R g hg hSg hx using hpiece
  have hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom) :=
    fun x => hP _ _ (hSg x)
  choose c hc using hc
  have key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q),
      Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c' := by
    intro x V g' c' h' v hv
    obtain ⟨u, hu⟩ := hx x
    exact huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have := hg x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩
    obtain ⟨u, hu⟩ := hx'
    exact key x' (g x) (c x) (hc x) u hu
  let ψ : LocallyConstant (PrimeSpectrum B) (ZMod q) := ⟨c, hlc⟩
  refine ⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩
  · exact Scheme.Cover.mem_grothendieckTopology
      (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g
        (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)
  · intro V k hk
    obtain ⟨W, h, k', hk', rfl⟩ := hk
    obtain ⟨x⟩ := hk'
    rw [res_comp, res_comp]
    congr 1
    rw [hc x]
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x)
    have hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x) := by
      ext u
      exact key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)
    have e := hm.1 B (R x) φ.hom ζ ψ
    rw [hlc', hm.2, LateralTheory.E.LCBijPf.gam_map] at e
    rw [← hφ]
    exact e.symm

end LateralTheory.E.DescentPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagCompPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagCompPf

theorem block_unique {A : Type} [CommRing A] (P R : PartDiagCut.Part A) (e : A) (he : e ∈ R.1) (a b : P.1)
    (ha : e * a.1 = e) (hb : e * b.1 = e) : a = b := by
  by_contra hne
  have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
  have h0 : a.1 * b.1 = 0 := P.orth a.1 a.2 b.1 b.2 hne'
  have : e = 0 := by
    calc e = e * a.1 * b.1 := by rw [ha, hb]
      _ = e * (a.1 * b.1) := by ring
      _ = 0 := by rw [h0, mul_zero]
  exact (R.idem e he).2 this

theorem par_trans {B : Type} [CommRing B] (I : Ideal B) {P Q R : PartDiagCut.Part (B ⧸ I)} (h1 : P ≤ Q) (h2 : Q ≤ R) (e : R.1) :
    par (h1.trans h2) e = par h1 (par h2 e) := by
  apply block_unique P R e.1 e.2
  · exact par_spec _ e
  · calc e.1 * (par h1 (par h2 e)).1 = e.1 * (par h2 e).1 * (par h1 (par h2 e)).1 := by rw [par_spec h2 e]
      _ = e.1 * ((par h2 e).1 * (par h1 (par h2 e)).1) := by ring
      _ = e.1 := by rw [par_spec h1 (par h2 e), par_spec h2 e]

theorem DiagComp_of : DiagComp := by
  intro B _ I P Q R h1 h2
  ext x e
  have key : ∀ (g g' : B →+* B), g = g' → ∀ (a b : P.1), a = b →
      ∀ (hA : S I a.1 ≤ (S I e.1).comap g) (hD : S I b.1 ≤ (S I e.1).comap g'),
      IsLocalization.map (M := S I a.1) (T := S I e.1) (Localization (S I e.1)) g hA (x a)
      = IsLocalization.map (M := S I b.1) (T := S I e.1) (Localization (S I e.1)) g' hD (x b) := by
    rintro g _ rfl a _ rfl hA hD; rfl
  simp only [stageMap, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  erw [IsLocalization.map_map]
  exact key _ _ (RingHom.id_comp _).symm _ _ (par_trans I h1 h2 e) _ _

end LateralTheory.E.DiagCompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagIdPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagIdPf

theorem par_self {A : Type} [CommRing A] {P : LateralTheory.E.PartDiagCut.Part A} (h : P ≤ P) (e : P.1) : par h e = e := by
  apply Subtype.ext
  by_contra hne
  have h1 := par_spec h e
  have h2 := P.orth e.1 e.2 (par h e).1 (par h e).2 (fun h' => hne h'.symm)
  exact (P.idem e.1 e.2).2 (h1.symm.trans h2)

theorem aux {B : Type} [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P) (e0 e : P.1) (hee : e0 = e)
    (hle : S I e0.1 ≤ (S I e.1).comap (RingHom.id B)) :
    IsLocalization.map (M := S I e0.1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B) hle (x e0) = x e := by
  subst hee
  exact IsLocalization.map_id _ _

theorem DiagId_of : LateralTheory.E.PartDiagCut.DiagId := by
  intro B _ I P h
  refine RingHom.ext fun x => funext fun e => ?_
  simp only [stageMap, RingHom.pi_apply, RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.id_apply]
  exact aux I P x (par h e) e (par_self h e) _

end LateralTheory.E.DiagIdPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagNatPf
section
namespace LateralTheory.E.DiagNatPf
open LateralTheory.E.PartDiagCut

theorem DiagNat_of : LateralTheory.E.PartDiagCut.DiagNat := by
  intro B _ I P Q h
  apply RingHom.ext
  intro b
  funext e
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact (IsLocalization.map_eq (S := Localization (S I (par h e).1)) _ b).trans (by rfl)

end LateralTheory.E.DiagNatPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueRelPfNat
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.GlueRelPfNat
variable (R : Type) [CommRing R]

theorem map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff φ₁ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.map, mappingCone.inl_desc,
      Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inl_fst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      mappingCone.inl_fst]
    simp
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp [mappingCone.map]

end LateralTheory.E.GlueRelPfNat
end
end

