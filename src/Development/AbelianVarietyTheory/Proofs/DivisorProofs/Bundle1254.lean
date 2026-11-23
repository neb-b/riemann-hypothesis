module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormRowSubProdMinors
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandard
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.SqRootPairing

theorem eq_of_sq_eq_of_odd {G : Type} [CommGroup G] {k : ℕ} (hk : Odd k) {a b : G} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (h : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul] at ha hb
  rw [h] at ha
  exact mul_left_cancel (ha.trans hb.symm)

theorem weilIs_down {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : Out.WeilIs G L k x₀ y₀ c) : Out.WeilIs G' L' k x y c := by
  subst hg
  exact (weilIs_grpPullback_of_comm _ _ _ _ _ _ _ _ hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem pow_eq_one (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {k n : ℕ} {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (H : Out.WeilIs P.A P.L k x y c) (hx : x ^ n = 1) : c ^ n = 1 := by
  have key : ∀ l : ℕ, Out.WeilIs P.A P.L k (x ^ (l + 1)) y (c ^ (l + 1)) := fun l => by
    induction l with
    | zero => rw [zero_add, pow_one, pow_one]; exact H
    | succ l ih => rw [pow_succ, pow_succ c]; exact (hL.weil S P k T).2.1 _ _ _ _ _ ih H
  have := key n
  rw [pow_succ, hx, _root_.one_mul] at this
  have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB this H
  rwa [pow_succ, mul_eq_right] at e

theorem weilIs_lev_of_sqOf : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  intro h k K _ ζ σ S s c p P φ lev hk3 hk hζ hp hsq hlev _ tors a b e he
  obtain ⟨hpb, -, φ₂, sq, iso⟩ := hsq
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let z : ℂˣ := Units.mk0 (σ ζ) (by rw [hζ]; exact Complex.exp_ne_zero _)
  have hz : (z : ℂ) = σ ζ := rfl
  have hzk : z ^ k = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hz, hζ, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hk0, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, Units.val_one])
  have hez : e = z ^ omegaStd a b := Units.ext (by
    rw [Units.val_zpow_eq_zpow_val, hz, hζ, ← Complex.exp_int_mul, he]
    congr 1
    ring)
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have dc : (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left).IsLB := LB.isLB_linComb c.isLB _ _
  have w₀ := (c.geom ℂ p σ z hp hz).2.2 a b
  have pt : ∀ a, (toUnit (Over.mk p) ≫ c.lev a).left = (lev a).left ≫ φ := fun a => by
    rw [hlev, Over.comp_left, Over.toUnit_left]
    rfl
  have w₁ := weilIs_down dc dg hpb (SiegelPull.diag_iso sq iso) (𝟙_ (Over (Sp ℂ))) p (Category.id_comp p).symm k
    (lev a) (lev b) _ _ _ (pt a) (pt b) w₀
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P k (𝟙_ (Over (Sp ℂ)))).1 (lev a) (lev b) (tors a) (tors b)
  have w₂ := SiegelOfPolarised.weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg
    (SiegelOfPolarised.lbIso_diag hL P) hc₀
  have e₂ := CommutatorPairing.weilIs_unique hL.globalFns P.isAb dg w₂ w₁
  have up : ∀ (u : ℂˣ) (n : ℕ), unitOn (u ^ n) = unitOn u ^ n := fun u n => map_pow _ _ _
  have e₁ : c₀ = unitOn e := by
    refine eq_of_sq_eq_of_odd hk (pow_eq_one hL P hc₀ (tors a)) ?_ (e₂.trans ?_)
    · refine (up e k).symm.trans ?_
      rw [hez, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzk, one_zpow]
      exact map_one _
    · refine Eq.trans ?_ (up e 2)
      rw [hez, mul_comm, zpow_mul, zpow_ofNat]
  exact e₁ ▸ hc₀

end GlobalTheory.SqRootPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadEndomorphismTorsionSectionEqSpecialisation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsCmp

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B]
    (x : 𝟙_ (Over S') ⟶ (Over.pullback f).obj B) (x₀ : 𝟙_ (Over S) ⟶ B)
    (hx : f ≫ x₀.left = x.left ≫ pullback.fst B.hom f) (N : ℕ) (h : x₀ ^ N = 1) : x ^ N = 1 := by
  have e : ∀ k, f ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst B.hom f := fun k =>
    GlobalTheory.ZH.MultInt.pow_left_pullback f B (T := 𝟙_ (Over S')) (T₀ := 𝟙_ (Over S)) f
      (by simp) x x₀ hx k
  have e0 := e 0
  have eN := e N
  rw [h, ← pow_zero x₀, e0] at eN
  rw [← pow_zero x]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact eN.symm
  · exact (Over.w (x ^ N)).trans (Over.w (x ^ 0)).symm

end GlobalTheory.TorsCmp


open GlobalTheory.TorsCmp in
theorem GlobalTheory.TorsCmp.torsion_section_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := by
  intro k₀ K _ _ _ _ B _ hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf N hN y₀ hy₀ c hc₁ hc₂
  haveI := hΨ
  haveI := hf₀
  haveI : IsAbelianScheme ((Over.pullback (spMap (algebraMap k₀ R))).obj B) :=
    by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      exact
        { comm := Functor.isCommMonObj_obj
          smooth := by change Smooth (pullback.snd B.hom _); infer_instance
          proper := by change IsProper (pullback.snd B.hom _); infer_instance
          geomConnected := by change GeometricallyConnected (pullback.snd B.hom _); infer_instance }
  have hgf : spMap g.toRingHom ≫ spMap (algebraMap k₀ R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : g.toRingHom.comp (algebraMap k₀ R) = RingHom.id k₀ := by
      ext r; exact g.commutes r
    rw [this]; exact Spec.map_id _
  have hNR : IsUnit (N : Γ(Sp R, ⊤)) := by
    have h1 : IsUnit (N : k₀) := Ne.isUnit hN
    have h2 : IsUnit (N : R) := by simpa using h1.map (algebraMap k₀ R)
    simpa using h2.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let cc : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk c (by exact hc₂)
  let bb : 𝟙_ (Over (Sp R)) ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk (pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left) (𝟙 _) (by
      rw [Category.assoc, Category.assoc, Over.w f₀, Over.w y₀, Category.id_comp]; rfl))
      (pullback.lift_snd _ _ _)
  have hcc : cc ^ N = 1 := pow_eq_one_of_pullback _ B cc y₀ hc₁.symm N hy₀
  have ha : (cc ≫ Ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hcc, MonObj.one_comp]
  have hb : bb ^ N = 1 := by
    refine pow_eq_one_of_pullback _ B bb (y₀ ≫ f₀) (pullback.lift_fst _ _ _).symm N ?_
    rw [← MonObj.pow_comp, hy₀, MonObj.one_comp]
  have hxc : spMap g.toRingHom ≫ c = y₀.left ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc₁, reassoc_of% hgf, Category.assoc, hσ₁, Category.comp_id]
    · rw [Category.assoc, hc₂, Category.assoc, hσ₂, ← Category.assoc, Over.w y₀]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hpt : spMap g.toRingHom ≫ (cc ≫ Ψ).left = spMap g.toRingHom ≫ bb.left := by
    apply pullback.hom_ext
    · change spMap g.toRingHom ≫ c ≫ Ψ.left ≫ _ = spMap g.toRingHom ≫ pullback.lift _ _ _ ≫ _
      rw [reassoc_of% hxc, ← hf, pullback.lift_fst, reassoc_of% hgf]
    · rw [Category.assoc, Category.assoc]
      exact congrArg _ ((Over.w (cc ≫ Ψ)).trans (Over.w bb).symm)
  have hab := GlobalTheory.HkFam.ListedSubgroup.section_eq _ hNR ha hb (spMap g.toRingHom) hpt
  have := congrArg (fun z => z.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ R))) hab
  simp only [cc, bb, Over.comp_left, Over.homMk_left, Category.assoc] at this
  simpa only [pullback.lift_fst] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProduct
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem substF_invT_minor_det {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} (X : Data P)
    (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ) (τ : D.what₂.Tau) (s : Fin P.a → Fin P.d) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det) =
      MvPolynomial.C ((G τ)⁻¹.det) * MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det := by
  set M := Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)
  set φ := GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
  set H : Matrix (Fin P.a) (Fin P.a) (MvPolynomial (FVar D X.B.rank X.A.rank) ℂ) :=
    Matrix.of fun i'' i' => MvPolynomial.C ((G τ)⁻¹ (Fin.cast X.rkA.symm i') (Fin.cast X.rkA.symm i''))
  have hH : H.det = MvPolynomial.C ((G τ)⁻¹.det) := by
    have e1 : H = (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D X.B.rank X.A.rank) ℂ).mapMatrix
        (((G τ)⁻¹.transpose).submatrix (finCongr X.rkA.symm) (finCongr X.rkA.symm)) := by
      ext i j; simp [H]
    rw [e1, ← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hM : ((φ.comp (MvPolynomial.rename X.var)).mapMatrix M) = (MvPolynomial.rename X.var).mapMatrix M * H := by
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, M, H, Matrix.of_apply, AlgHom.comp_apply,
      MvPolynomial.rename_X, φ, GlobalTheory.CompactHowe.substF_X, Data.var]
    rw [Finset.sum_eq_single (Fin.cast X.rkB.symm (s i))]
    · simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
      exact Fintype.sum_equiv (finCongr X.rkA) _ _ (fun l => by simp [mul_comm])
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  have := AlgHom.map_det (φ.comp (MvPolynomial.rename X.var)) M
  rw [AlgHom.comp_apply] at this
  rw [this, hM, Matrix.det_mul, hH, ← AlgHom.map_det, mul_comm]

end GlobalTheory.NormDict

namespace GlobalTheory.NormDict

theorem substF_invT_minorPol : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  intro D cc δ t0 Q P X T G
  rw [minorPol, map_prod, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  simp only [substF_invT_minor_det, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

end GlobalTheory.NormDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionMaximalMinorProductEqSumCauchyBinet
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem substF_minorPol_eq_sum : ∀ (D : D7) {a d : ℕ} {m : D.what₂.Tau → ℕ} (K : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ)
    (T : Tup D a d m), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (minorPol D T) =
      ∑ T' : Tup D a d m, (∏ τ, ∏ r, (Matrix.of fun i i' : Fin a => K τ ((T' τ r).1 i') ((T τ r).1 i)).det) •
        minorPol D T' := by
  intro D a d m K T
  have hmin : ∀ τ (s : Fin a → Fin d), GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))
      (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det =
      ∑ s' : {s : Fin a → Fin d // StrictMono s},
        MvPolynomial.C ((Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)).det) *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s'.1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det]
    have hM : (GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ))).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
        (Matrix.of fun (i : Fin a) (k : Fin d) => (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) *
        (Matrix.of fun (k : Fin d) (i' : Fin a) => (MvPolynomial.X (τ, k, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) := by
      refine Matrix.ext fun i i' => ?_
      simp only [RingHom.mapMatrix_apply, AlgHom.coe_toRingHom, Matrix.map_apply, Matrix.of_apply,
        GlobalTheory.CompactHowe.substF_X, Matrix.mul_apply, Matrix.one_apply]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single i']
      · simp
      · intro l _ hl; simp [Matrix.one_apply_ne hl]
      · simp
    rw [hM, GlobalTheory.MinorFrame.det_mul_eq_sum_sm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    congr 1
    rw [show (Matrix.of fun (i : Fin a) (k : Fin d) =>
        (MvPolynomial.C (K τ k (s i)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).submatrix id s'.1 =
        (MvPolynomial.C : ℂ →+* MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ).mapMatrix
          (Matrix.of fun i i' : Fin a => K τ (s'.1 i') (s i)) from by ext; simp]
    rw [← RingHom.map_det]
  unfold minorPol
  simp only [map_prod, hmin]
  rw [Finset.prod_congr rfl fun τ _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [← MvPolynomial.C_mul']
  simp only [Finset.prod_mul_distrib, map_prod]

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormEqDot
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Matrix

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace GlobalTheory.HermFamFrame

def formRight {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : V →+ ℂ :=
  AddMonoidHom.mk' (nm.form σ x) (nm.add_right σ x)

theorem form_sum_right {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ x (∑ j ∈ s, a j • w j) = ∑ j ∈ s, σ (a j) * nm.form σ x (w j) := by
  have := map_sum (formRight nm σ x) (fun j => a j • w j) s
  simp only [formRight, AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => nm.smul_right σ (a j) x (w j)

theorem form_sum_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (y : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ (∑ i ∈ s, a i • w i) y = ∑ i ∈ s, starRingEnd ℂ (σ (a i)) * nm.form σ (w i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← nm.conj_symm, form_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, nm.conj_symm]

end GlobalTheory.HermFamFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompMulLeftX
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.CCRFock

theorem pderiv_rename_prodMk_of_ne {W Λ : Type} {v w : W} (h : v ≠ w) (l : Λ) (r : MvPolynomial Λ ℂ) :
    MvPolynomial.pderiv (w, l) (MvPolynomial.rename (Prod.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Prod.fst e)

theorem pderiv_prod_rename_of_notMem {W Λ : Type} {w : W} (l : Λ) (q : W → MvPolynomial Λ ℂ) (s : Finset W)
    (hs : w ∉ s) :
    MvPolynomial.pderiv (w, l) (∏ v ∈ s, MvPolynomial.rename (Prod.mk v) (q v)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_prodMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMap_comp_atPl_pderiv (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ) :
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  apply PiTensorProduct.ext
  ext1 q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, polMap, atPl, PiTensorProduct.map_tprod,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i)
      ((Function.update (fun _ : W => (LinearMap.id : MvPolynomial Λ ℂ →ₗ[ℂ] MvPolynomial Λ ℂ)) w
        (MvPolynomial.pderiv l).toLinearMap i) (q i)) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Prod.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), LinearMap.id_apply]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename (Prod.mk_right_injective w) l (q w)]
  simp [mul_comm]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodConstantPolynomialsNeZero
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem tprod_one_pol_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (P Q R S : ℕ),
    (PiTensorProduct.tprod ℂ fun _ : InfinitePlace F => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ≠ 0 := by
  intro F _ _ P Q R S h
  let c : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ := (MvPolynomial.aeval (fun _ => (0:ℂ))).toLinearMap
  have key := congrArg (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ (InfinitePlace F) ℂ).compLinearMap (fun _ => c))) h
  simp [PiTensorProduct.lift.tprod, c] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecompositionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_place_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J), ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
    ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  first | exact @GlobalTheory.UnitaryPlaceSplit.exists_split_at | exact GlobalTheory.UnitaryPlaceSplit.exists_split_at | (intros; apply GlobalTheory.UnitaryPlaceSplit.exists_split_at <;> assumption)
end

