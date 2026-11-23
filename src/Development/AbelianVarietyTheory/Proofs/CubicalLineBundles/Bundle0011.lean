module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.CongrOrbit

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {S : Type} [CommRing S]

theorem scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem exists_unit_of_generators {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem frBor_of_eq [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : y'.u = y.u) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  subst hu
  obtain ⟨u0, hu0⟩ := exists_unit_of_generators (x := y.x) y.s s' y.gen gen'
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  classical
  refine ⟨fun o => match o with
    | none => u0
    | some _ => 1, rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · dsimp only
    rw [hu τ, hcomb]
    simp [Pi.single_apply]
  · intro i h
    simp only
    rw [← hu0 i]
    simp only [Scheme.Hom.appLE]
    have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
    rw [e]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

end Frames

theorem perFr_lact {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
      Formalism.L2.PjFree.perFr X x v τ i := by
  have hm : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := fun _ => rfl
  unfold Formalism.L2.PjFree.perFr
  simp only [hm, PerMove.emb_mulVec]
  split_ifs with h1 h2 h3 h4
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.mapMatrix)
    rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
      Matrix.mul_one]
  · rfl
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

noncomputable def latAut {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) : Λ ≃ₗ[𝓞 E] Λ where
  toFun a := ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).1 a.2⟩
  invFun a := ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ a, (h _).2 (by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact a.2)⟩
  map_add' a b := Subtype.ext (Matrix.mulVec_add (γ : Matrix (Fin r) (Fin r) E) (a : Fin r → E) (b : Fin r → E))
  map_smul' s a := Subtype.ext (Matrix.mulVec_smul (γ : Matrix (Fin r) (Fin r) E) s (a : Fin r → E))
  left_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
  right_inv a := Subtype.ext (by
    simp only
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])

end GlobalTheory.CongrOrbit

namespace GlobalTheory


open CongrOrbit in
theorem congr_lact_mem_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → l.A = 1 → ∀ k (γ : GL (Fin r) E), IsUStab (U.X k).Gm (U.X k).Λ γ → (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (l.M : E) • y) → ∀ x ∈ (U.X k).dom, ∃ γ' ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  intro E _ _ _ H Dw l Xo c σ r U hU hA k γ hγ hM x hx
  obtain ⟨-, -, -, hfib, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  have hx' := dom_lact (U.X k) hx hγ
  obtain ⟨P, hP, hPer, hu, hd, -⟩ := hpt k ⟨x, hx⟩
  obtain ⟨P', hP', hPer', hu', hd', -⟩ := hpt k ⟨_, hx'⟩
  let gam := (φ k).trans ((latAut (U.X k).Λ γ hγ.2).trans (φ k).symm)
  have hgam : ∀ a, (φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := by
    intro a
    simp only [gam, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨-, hpt, hex⟩ := FamRigid.ex_eq_of_level_group latMinkowski E H Dw l Xo _ g _ F (ik k) P P' gam 1
    hPer hPer' (fun a b => by
      have := hEF k (gam a) (gam b)
      rw [hgam, hgam, hγ.1, ← hEF] at this
      exact_mod_cast this)
    (fun a _ => by
      obtain ⟨y, hy, he⟩ := hM _ (φ k a).2
      refine ⟨(φ k).symm ⟨y, hy⟩, (φ k).injective (Subtype.ext ?_)⟩
      rw [hgam, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Submodule.coe_add, ← sub_eq_iff_eq_add', he,
        Nat.cast_smul_eq_nsmul]
      rfl)
    (fun a => ⟨gam a - a, by rw [hA, one_smul]; abel⟩)
    (fun a => by
      funext j
      rw [Matrix.one_mulVec, hP, hP', hgam]
      exact perFr_lact _ _ _ hγ.1 _ _ _)
  simp only [Matrix.one_mulVec] at hex
  obtain ⟨γ', hγ', b, hb, he⟩ := (hfib k k ⟨x, hx⟩ ⟨_, hx'⟩).1 (frBor_of_eq _ _
    (hu'.trans (hpt.symm.trans hu.symm)) (by
      funext τ i
      have h1 := hd' τ i
      simp only [hex] at h1
      exact VerticalDeriv.isDerivAt0_unique h1 (hd τ i)))
  exact ⟨γ', hγ', b, hb, eq_of_heq (Sigma.mk.inj he).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocalFibre

theorem connectedSpace_sp (R : Type) [CommRing R] [IsLocalRing R] : ConnectedSpace (Sp R) := by
  have h : _root_.IsConnected (Set.univ : Set (PrimeSpectrum R)) := by
    refine ⟨⟨IsLocalRing.closedPoint R, trivial⟩, isPreconnected_of_forall (IsLocalRing.closedPoint R) fun x _ => ?_⟩
    exact ⟨closure {x}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint x).mem_closure,
      subset_closure rfl, isPreconnected_singleton.closure⟩
  exact (connectedSpace_iff_univ.2 h : ConnectedSpace (PrimeSpectrum R))

theorem exists_polAV_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    {t : SAB H S} (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L)
    {R : Type} [CommRing R] [IsLocalRing R] {y : Sp R ⟶ S} {t' : SAB H (Sp R)} (m : SABMap t' t y) :
    ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ t.G.left) (act : OAct (𝓞 E) P.A),
      IsGrpPullback P.A t.G y φ ∧ LBIso P.L (t.PP.L.pull φ) ∧ ∀ a, (act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, g, -⟩ := m.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have am := relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hy hA
  have kt := kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) hK
  have := connectedSpace_sp R
  have : ConnectedSpace t'.G.left := GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (IsLocalRing.closedPoint R))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  exact ⟨{ A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
           isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp, ‹_›⟩
           rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
           sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ },
    m.φ, t'.act, m.cart, ⟨w, g⟩, m.act⟩

end GlobalTheory.LocalFibre

namespace GlobalTheory

theorem exists_polAV_pullback_of_isLocalRing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom →
      Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ S),
      ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ t.G.left) (act : OAct (𝓞 E) P.A),
        IsGrpPullback P.A t.G y φ ∧ LBIso P.L (t.PP.L.pull φ) ∧
          ∀ a, (act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro E _ _ _ H S t hp hA hK R _ _ y
  have h := isGrpPullback_pullback t.G y
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S (Sp R) t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback y t.G t.act).act a).left ≫ pullback.fst t.G.hom y =
      pullback.fst t.G.hom y ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R)} (x : T ⟶ (Over.pullback y).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback y t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have hsemi : IsSemiAbelian ((Over.pullback y).obj t.G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := t.semi.comm; infer_instance
    · have := t.semi.smooth; change Smooth (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.separated; change IsSeparated (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.quasiCompact; change QuasiCompact (pullback.snd t.G.hom y); infer_instance
    · have := t.semi.geomConnected; change GeometricallyConnected (pullback.snd t.G.hom y); infer_instance
    · intro Ω _ _ q
      obtain ⟨F⟩ := t.semi.fibres Ω (q ≫ y)
      exact ⟨torusExtOfIso (pullCompIso q y t.G) F⟩
  refine LocalFibre.exists_polAV_of_sabMap hp hA hK (t' :=
    ⟨(Over.pullback y).obj t.G, hsemi,
      OAct.pullback y t.G t.act, (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, ?_, ?_⟩) ?_
  · intro a
    let U := lift (pushPt h.1.w (fst ((Over.pullback y).obj t.G) ((Over.pullback y).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback y).obj t.G) ((Over.pullback y).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  ·
    let U := pushPt h.1.w (𝟙 ((Over.pullback y).obj t.G))
    refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  · exact ⟨cubeMapOf h, h, rfl, hact, hc'⟩

end GlobalTheory
end

