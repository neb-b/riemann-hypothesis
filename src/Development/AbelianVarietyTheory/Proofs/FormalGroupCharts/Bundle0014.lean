module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ActStOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartAction

theorem rep_unique (hR : RepSt) {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ}
    {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {κ : Type} [Finite κ] {a b : Fin d → MvPowerSeries κ R}
    {y z : Fam G κ} (ha : Rep x a y) (hb : Rep x b z) (h : y = z) : a = b := by
  subst h
  obtain ⟨-, h2, h3, -⟩ := hR R G d x hx κ
  exact (h2 y (h3 a y ha)).unique ha hb

theorem actSt_of (_ : JetAlgSt) (hR : RepSt) (hM : MapSt) : ActSt := by
  intro R _ G _ _ d x hx O _ act Gl hF
  have hex : ∀ a, ∃ φ, IsMapOf x x (act.act a) φ := fun a => by
    haveI := act.hom a
    exact (hM R G G d x x hx hx (act.act a) (IsMonHom.one_hom _)).exists
  choose φ hφ using hex
  have hpt : ∀ (n : ℕ) (j : Fin n), ∃ y, Rep x (pt R (n := n) d j) y := fun n j =>
    ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose y hy using hpt
  have h1 : ∀ a, Rep x (φ a) (fun m => y 1 0 m ≫ act.act a) := fun a => by
    have := (hφ a).2 1 _ _ (hy 1 0)
    rwa [gt_comp1_pt_right] at this
  refine ⟨⟨φ, fun a => (hφ a).1, fun a => ?_, fun a b => ?_, fun a b => ?_, ?_⟩, hφ⟩
  · haveI := act.hom a
    refine rep_unique hR hx ((hφ a).2 2 _ _ (hF.2 2 _ _ _ _ (hy 2 0) (hy 2 1)))
      (hF.2 2 _ _ _ _ ((hφ a).2 2 _ _ (hy 2 0)) ((hφ a).2 2 _ _ (hy 2 1))) ?_
    funext m
    exact MonObj.mul_comp _ _ _
  · refine rep_unique hR hx (h1 (a + b)) (hF.2 1 _ _ _ _ (h1 a) (h1 b)) ?_
    funext m
    rw [act.add]
    exact MonObj.comp_mul _ _ _
  · refine rep_unique hR hx (h1 (a * b)) ((hφ a).2 1 _ _ (h1 b)) ?_
    funext m
    rw [mul_comm, act.mul, Category.assoc]
  · refine rep_unique hR hx (h1 1) (hy 1 0) ?_
    funext m
    rw [act.one, Category.comp_id]

end GlobalTheory.ChartAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AddOfPtPt
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.mul {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y z : Fam G κ} (hy : IsFPt y) (hz : IsFPt z) : IsFPt (fun m => y m * z m : Fam G κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show _ ≫ (y (m + 1) * z (m + 1)) = y m * z m
    rw [MonObj.comp_mul, hy.1 m, hz.1 m]
  · show _ ≫ (y m * z m) = 1
    rw [MonObj.comp_mul, hy.2 m, hz.2 m, _root_.mul_one]

theorem addOf_pt_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  have h : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  unfold addOf
  rw [h]
  unfold ev
  exact congrFun MvPowerSeries.subst_self _

theorem lawSt_of (hJ : JetAlgSt) (hR : RepSt) : LawSt := by
  intro R _ G _ _ d x hx
  have uC : ∀ {n : ℕ} {a a' : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a' y → a = a' :=
    fun {n a a' y} h h' =>
      ((hR R G d x hx (Fin n × Fin d)).2.1 y ((hR R G d x hx (Fin n × Fin d)).2.2.1 a y h)).unique h h'
  have uP : ∀ {n : ℕ} {a : Pt R n d} {y y' : Fam G (Fin n × Fin d)}, Rep x a y → Rep x a y' → y = y' :=
    fun {n a y y'} h h' => ((hR R G d x hx (Fin n × Fin d)).1 a h.1).unique h h'
  have gen : ∀ (n : ℕ) (j : Fin n), ∃ y : Fam G (Fin n × Fin d), Rep x (pt R d j) y :=
    fun n j => ((hR R G d x hx (Fin n × Fin d)).1 _ (gp_pt j)).exists
  choose Y hY using gen
  refine ⟨?_, fun F F' hF hF' => ?_⟩
  swap
  · rw [← addOf_pt_pt F, ← addOf_pt_pt F']
    exact uC (hF.2 2 _ _ _ _ (hY 2 0) (hY 2 1)) (hF'.2 2 _ _ _ _ (hY 2 0) (hY 2 1))
  have H2 := hR R G d x hx (Fin 2 × Fin d)
  obtain ⟨F, hF⟩ := (H2.2.1 _ (IsFPt.mul (H2.2.2.1 _ _ (hY 2 0)) (H2.2.2.1 _ _ (hY 2 1)))).exists
  have law : IsLawOf x F := by
    refine ⟨hF.1, fun n a b y z ha hb => ?_⟩
    let c : Fin 2 × Fin d → PS R n d := fun p => (![a, b] : Fin 2 → Pt R n d) p.1 p.2
    have hc : ∀ p, constantCoeff (c p) = 0 := fun p => pair_points_zero_constant ha.1 hb.1 p.1 p.2
    have hex : ∀ m, ∃ ψ : JetR R (Fin 2 × Fin d) m →ₐ[R] JetR R (Fin n × Fin d) m,
        ∀ j, ψ (zR m j) = toJet m (c j) :=
      fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 2 × Fin d) c hc m).1
    choose ψ hψ using hex
    have sub := H2.2.2.2.2 (Fin n × Fin d) c ψ hc hψ
    have hs : ∀ j : Fin 2, (fun i => MvPowerSeries.subst c (pt R (n := 2) d j i)) = (![a, b] : Fin 2 → Pt R n d) j :=
      fun j => funext fun i => gt_ev_X _ (pair_points_zero_constant ha.1 hb.1) j i
    have e0 : (fun m => spMap (ψ m) ≫ Y 2 0 m) = y := by
      have := sub _ _ (hY 2 0)
      rw [hs 0] at this
      exact uP this ha
    have e1 : (fun m => spMap (ψ m) ≫ Y 2 1 m) = z := by
      have := sub _ _ (hY 2 1)
      rw [hs 1] at this
      exact uP this hb
    have key := sub _ _ hF
    have e : (fun m => spMap (ψ m) ≫ (Y 2 0 m * Y 2 1 m)) = fun m => y m * z m := by
      funext m
      rw [MonObj.comp_mul, ← e0, ← e1]
    rw [← e]
    exact key
  refine ⟨⟨F, hF.1, fun i => ?_, fun i => ?_, fun i => ?_⟩, law⟩
  · have h := law.2 1 _ _ _ _ (hR R G d x hx (Fin 1 × Fin d)).2.2.2.1 (hY 1 0)
    simp only [_root_.one_mul] at h
    exact congrFun (uC h (hY 1 0)) i
  · have h := law.2 2 _ _ _ _ (hY 2 1) (hY 2 0)
    have e : (fun m => Y 2 1 m * Y 2 0 m) = fun m => Y 2 0 m * Y 2 1 m :=
      funext fun m => _root_.mul_comm _ _
    rw [e] at h
    exact congrFun (uC h hF) i
  · have h := law.2 3 _ _ _ _ (law.2 3 _ _ _ _ (hY 3 0) (hY 3 1)) (hY 3 2)
    have h' := law.2 3 _ _ _ _ (hY 3 0) (law.2 3 _ _ _ _ (hY 3 1) (hY 3 2))
    simp only [_root_.mul_assoc] at h
    exact congrFun (uC h h') i

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DetJacobianFormalMulNEqPowMulUnit
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace GlobalTheory.MulJacobian

variable {R : Type} [CommRing R] {d : ℕ}

theorem mulF_eq_mulN (G : FGLaw R d) (N : ℕ) : mulF G.F N = mulN G N := by
  induction N with
  | zero => rfl
  | succ n ih => rw [mulF, mulN, ih]

def invMat (G : FGLaw R d) : Matrix (Fin d) (Fin d) (PS R 1 d) :=
  Matrix.of fun j i => ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F j))

theorem const_invMat (G : FGLaw R d) (j i : Fin d) :
    constantCoeff (invMat G j i) = (1 : Matrix (Fin d) (Fin d) R) j i := by
  rw [invMat, Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev GlobalTheory.ChartTrans.axis_GP,
    ← GlobalTheory.FormalMulN.coeff_single_one, GlobalTheory.FormalMulN.lin_F_right, Matrix.one_apply]

theorem isUnit_det_of_const {σ : Type} (M : Matrix (Fin d) (Fin d) (MvPowerSeries σ R))
    (h : ∀ j i, constantCoeff (M j i) = (1 : Matrix (Fin d) (Fin d) R) j i) : IsUnit M.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff (σ := σ) (R := R)).mapMatrix M = 1 := by
    ext j i
    exact h j i
  rw [this, Matrix.det_one]
  exact isUnit_one

theorem dof_single (G : FGLaw R d) (c : R) (l : Fin d) (f : PS R 1 d) :
    Dof G.F (Pi.single l c) f = C c * ∑ j, pderiv ((0 : Fin 1), j) f * invMat G j l := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, invMat, Matrix.of_apply]
    ring
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, map_zero, zero_mul]
  · simp

theorem jac_mul_invMat (G : FGLaw R d) (N : ℕ) :
    (Matrix.of fun i j : Fin d => pderiv ((0 : Fin 1), j) (mulN G N i)) * invMat G =
      (N : PS R 1 d) • Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.FormalMulN.mulN_hom R d G N
  have hφ : GP (mulN G N) := h0
  ext1 i l
  have h := GlobalTheory.HomChain.dof_hom G G (mulN G N) h0 h1 (Pi.single l 1) (pt R d 0 i)
  have e1 : (dLin (mulN G N)).mulVec (Pi.single l 1) = Pi.single l (N : R) := by
    rw [h2, Matrix.smul_mulVec, Matrix.one_mulVec, ← Pi.single_smul, smul_eq_mul, mul_one]
  have e2 : ev (n := 1) ![mulN G N] (pt R d 0 i) = mulN G N i :=
    GlobalTheory.GaugeAdjoint.ev_pt (single_point_zero_constant hφ) 0 i
  have e3 : ∑ j, pderiv ((0 : Fin 1), j) (pt R (n := 1) d 0 i) * invMat G j l = invMat G i l := by
    rw [Finset.sum_eq_single i]
    · simp [pt]
    · intro j _ hj
      rw [pt, pderiv_X_of_ne (by simpa using hj.symm), zero_mul]
    · simp
  rw [e1, e2, dof_single, dof_single, e3, GlobalTheory.ChartTrans.ev_C_mul _ (single_point_zero_constant hφ), map_one, one_mul,
    map_natCast] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  exact h

theorem det_jac_mulF : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ),
    ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  intro R _ d G N
  have hφ : GP (mulN G N) := GlobalTheory.FormalMulN.const_mulN G N
  obtain ⟨a, ha⟩ := isUnit_det_of_const (invMat G) (const_invMat G)
  obtain ⟨b, hb⟩ := isUnit_det_of_const
    (Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l)) (fun i l => by
      rw [Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev (single_point_zero_constant hφ), const_invMat])
  have h := congrArg Matrix.det (jac_mul_invMat G N)
  rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, ← ha, ← hb] at h
  refine ⟨b * a⁻¹, ?_⟩
  rw [mulF_eq_mulN, Units.val_mul, ← mul_assoc, ← h, Units.mul_inv_cancel_right]

end GlobalTheory.MulJacobian
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExUniqueSer
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer

theorem IsFPt.zero_eq_one {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type}
    {y : Fam G κ} (hy : IsFPt y) : y 0 = 1 := by
  have hc : (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ 0) = AlgHom.id R _ := by
    apply jet_ext
    intro j
    rw [AlgHom.comp_apply, jetAug_zR, map_zero]
    apply jetAug_zero_injective κ
    rw [map_zero, AlgHom.id_apply, jetAug_zR]
  have hid : spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    rw [spMap_left]
    exact Spec.map_id _
  calc y 0 = spMap (R₀ := R) (AlgHom.id R (JetR R κ 0)) ≫ y 0 := by rw [hid, Category.id_comp]
    _ = spMap (Algebra.ofId R (JetR R κ 0)) ≫ spMap (jetAug R κ 0) ≫ y 0 := by
      rw [← Category.assoc, spMap_comp, hc]
    _ = 1 := by rw [hy.2 0]; exact MonObj.comp_one _

theorem exUnique_ser (hJ : JetAlgSt) (hR : RepSt) (hS : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {k : ℕ} {Y : Over (Spec (CommRingCat.of R))}
    (L : ∀ T : Over (Spec (CommRingCat.of R)), (Fin k → (T ⟶ G)) → (T ⟶ Y))
    (hL : ∀ (T T' : Over (Spec (CommRingCat.of R))) (h : T' ⟶ T) (y : Fin k → (T ⟶ G)),
      h ≫ L T y = L T' (fun j => h ≫ y j))
    (U : Y.left.Opens) (hU : ⊤ ≤ (L _ (fun _ => η[G])).left ⁻¹ᵁ U) (f : Γ(Y.left, U)) :
    ∃! g : PS R k d, ∀ (n : ℕ) (a : Fin k → Pt R n d) (y : Fin k → Fam G (Fin n × Fin d)),
      (∀ j, Rep x (a j) (y j)) → HasSer (fun m => (L _ (fun j => y j m)).left) U f (ev a g) := by
  obtain ⟨h1, -, h3, -, h5⟩ := hR R G d x hx (Fin k × Fin d)
  have hpt : ∀ (j : Fin k) (i : Fin d), constantCoeff (pt R (n := k) d j i) = 0 :=
    fun j => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt j
  choose y₀ hy₀ using fun j : Fin k => (h1 (pt R (n := k) d j) (hpt j)).exists
  have hF : ∀ j, IsFPt (y₀ j) := fun j => h3 _ _ (hy₀ j)
  have hcomp : ∀ m, (spMap (jetTruncR R (Fin k × Fin d) m)).left ≫ (L _ (fun j => y₀ j (m + 1))).left =
      (L _ (fun j => y₀ j m)).left := by
    intro m
    rw [← Over.comp_left, hL]
    congr 2
    funext j
    exact (hF j).1 m
  have h0 : ⊤ ≤ (L _ (fun j => y₀ j 0)).left ⁻¹ᵁ U := by
    have e : L _ (fun j => y₀ j 0) = toUnit _ ≫ L _ (fun _ => η[G]) := by
      rw [hL]
      congr 1
      funext j
      exact (hF j).zero_eq_one
    rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
    intro p _
    exact hU (Set.mem_univ _)
  obtain ⟨⟨τ, hτ⟩, -, -, hsub⟩ :=
    hS R (Fin k × Fin d) Y.left (fun m => (L _ (fun j => y₀ j m)).left) hcomp U h0
  refine ⟨τ f, fun n a y hy => ?_, fun g hg => ?_⟩
  · let b : Fin k × Fin d → MvPowerSeries (Fin n × Fin d) R := fun p => a p.1 p.2
    have hb : ∀ p, constantCoeff (b p) = 0 := fun p => (hy p.1).1 p.2
    choose ψ hψ using fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin k × Fin d) b hb m).1
    have hyy : ∀ j, y j = fun m => spMap (ψ m) ≫ y₀ j m := by
      intro j
      have r := h5 (Fin n × Fin d) b ψ hb hψ _ _ (hy₀ j)
      have e : (fun i => MvPowerSeries.subst b (pt R (n := k) d j i)) = a j := by
        funext i
        exact MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hb) (j, i)
      rw [e] at r
      exact ((hR R G d x hx (Fin n × Fin d)).1 (a j) (hy j).1).unique (hy j) r
    have r := hsub (Fin n × Fin d) b ψ hb hψ f (τ f) ((hτ f _).2 rfl)
    have e : (fun m => (L _ (fun j => y j m)).left) =
        fun m => (spMap (ψ m)).left ≫ (L _ (fun j => y₀ j m)).left := by
      funext m
      rw [← Over.comp_left, hL]
      simp only [hyy]
    rw [e]
    exact r
  · have r := hg k (fun j => pt R (n := k) d j) y₀ hy₀
    have e : ev (fun j => pt R (n := k) d j) g = g := by
      unfold ev
      exact congrFun MvPowerSeries.subst_self g
    rw [e] at r
    exact (hτ f g).1 r

theorem serEx : JetAlgSt → RepSt → SerSt → SerExSt := by
  intro hJ hR hS R _ G _ d x hx
  refine ⟨fun U hU f => ?_, fun U hU f => ?_, fun U hU f => ?_⟩
  · have H := exUnique_ser hJ hR hS hx (k := 1) (Y := G) (fun _ y => y 0) (fun _ _ _ _ => rfl) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a y ha => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a] ![y] (fun j => by fin_cases j; exact ha)
    · have e : a = ![a 0] := by funext j; fin_cases j; rfl
      rw [e]
      exact h n (a 0) (y 0) (ha 0)
  · have H := exUnique_ser hJ hR hS hx (k := 2) (Y := G ⊗ G) (fun _ y => lift (y 0) (y 1))
      (fun _ _ _ _ => comp_lift _ _ _) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b y z ha hb => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b] ![y, z] (fun j => by fin_cases j; exacts [ha, hb])
    · have e : a = ![a 0, a 1] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (y 0) (y 1) (ha 0) (ha 1)
  · have H := exUnique_ser hJ hR hS hx (k := 3) (Y := G ⊗ G ⊗ G)
      (fun _ y => lift (y 0) (lift (y 1) (y 2)))
      (fun _ _ _ _ => by rw [comp_lift, comp_lift]) U hU f
    refine (existsUnique_congr fun g => ⟨fun h n a b c y z w ha hb hc => ?_, fun h n a y ha => ?_⟩).1 H
    · exact h n ![a, b, c] ![y, z, w] (fun j => by fin_cases j; exacts [ha, hb, hc])
    · have e : a = ![a 0, a 1, a 2] := by funext j; fin_cases j <;> rfl
      rw [e]
      exact h n (a 0) (a 1) (a 2) (y 0) (y 1) (y 2) (ha 0) (ha 1) (ha 2)

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NormRos

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))), t.IsGen := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  refine ⟨⟨fun j => res (le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩,
    fun (p q : K' ⊕ K → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]

theorem gen_s_ext {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u (𝟙 Y) y J = val u' (𝟙 Y) y J) : u.s = u'.s :=
  funext fun j => Units.ext (sec_ext_val hL (s := genSec u hu) (s' := genSec u' hu') (fun y J hJ => by
    rw [sval_genSec u hu _ y hJ, sval_genSec u' hu' _ y hJ, h y J hJ]) j)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem prod_square {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_gen_rosati {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L)) :
    ∃ t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε), t.IsGen := by
  obtain ⟨t, ht⟩ := exists_gen_of_lbIso H
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε) (fun V _ k => by
      have p := prod_ros f g (fst G G) (snd G G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2)))
        (U := V) _ (prod_square (fst G G) (snd G G ≫ g) k)
        (DVR.prod_neg _ _ (prod_square (fst G G ≫ f) (snd G G) k)))).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
  exact ⟨u, hu⟩

theorem exists_isNormRos {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)) (ht : t.IsGen) : ∃ u, IsNormRos L f g u := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := rosatiφ G f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ G f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_⟩
  have e : zero2 G ≫ (lift (1 : G ⊗ G ⟶ G) (1 : G ⊗ G ⟶ G)).left = zero2 G := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
    congr 1
  rw [val_one, val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]


omit [IsCommMonObj G] in
theorem isNormRos_unique {L : LB G.left} (hL : L.IsLB) (f g : G ⟶ G)
    (hs : Function.Surjective (G ⊗ G).hom.appTop.hom) {u u' : LB.Gen (LB.LinComb L (rosatiφ G f g) rosatiε)}
    (h : IsNormRos L f g u) (h' : IsNormRos L f g u') : u.s = u'.s := by
  have z2 : zero2 G ≫ (G ⊗ G).hom = 𝟙 S := Over.w (lift η[G] η[G])
  refine gen_s_ext hL h.1 h'.1 fun y J hJ =>
    gen_unique hL (S₀ := S) (G ⊗ G).hom (zero2 G) z2 hs h.1 h'.1 (fun s I hI => ?_) _ _ y J hJ
  have a := val_corr hI h.2 (𝟙 _)
  have b := val_corr hI h'.2 (𝟙 _)
  rw [val_pull hI, Category.id_comp, val_one] at a b
  exact a.trans b.symm

theorem normRos_of_lbIso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB →
    ∀ (f g : G ⟶ G) [IsMonHom f] [IsMonHom g],
    LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) →
    (∃ u, IsNormRos L f g u) ∧ (Function.Surjective (G ⊗ G).hom.appTop.hom →
      ∀ u u', IsNormRos L f g u → IsNormRos L f g u' → u.s = u'.s) := by
  intro S G _ _ L hL f g _ _ H
  obtain ⟨t, ht⟩ := exists_gen_rosati hL f g H
  exact ⟨exists_isNormRos hL f g t ht, fun hs u u' h h' => isNormRos_unique hL f g hs h h'⟩

end GlobalTheory.NormRos
end
end

