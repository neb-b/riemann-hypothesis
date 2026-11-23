module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteProjBundleModelCohomologyEquivProdFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFra
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section

namespace GlobalTheory.TorusFrame

theorem gram_mul_of_preserves {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M x : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * x) = ReciprocityTheory.ChartRestriction.G.FD.gram τ G x := by
  have hc (a : Fin r) : ReciprocityTheory.ChartRestriction.G.FD.col (M * x) a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col x a := by
    ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply, hc, hM]

theorem torus_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  intro E _ _ _ r X x hx
  refine ⟨fun θ => ⟨torusGL hx θ, _root_.GlobalTheory.TorusFrame.torusGL_mem_realSU E r X x hx θ⟩, torusDer x, ?_, ?_, ?_, ?_, fun θ => _root_.GlobalTheory.TorusFrame.torusDer_mem_realLie_and_inFrame E r X x hx θ, ?_⟩
  · intro θ; funext τ
    show ((mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ) = (mat x τ * mat (phaseFrame θ) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]; rfl
  · intro θ θ'
    refine Subtype.ext (funext fun τ => ?_)
    have hp : phaseU ((θ + θ') τ) = phaseU (θ τ) * phaseU (θ' τ) := by
      refine Units.ext ?_
      simp only [phaseU, Units.val_mul, diagonal_mul_diagonal, Pi.add_apply, angles_add, Complex.ofReal_add,
        mul_add, Complex.exp_add]
    simp only [Subgroup.coe_mul, Pi.mul_apply, torusGL, hp]
    group
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    have hph : Continuous fun φ : Fin (r - 1) → ℝ => phaseU φ := by
      refine Units.continuous_iff.2 ⟨Continuous.matrix_diagonal (continuous_pi fun a => ?_),
        Continuous.matrix_diagonal (continuous_pi fun a => ?_)⟩
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a)))
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a))).neg
    exact (continuous_const.mul (hph.comp (continuous_apply τ))).mul continuous_const
  · exact _root_.GlobalTheory.TorusFrame.hasStrictFDerivAt_torus_zero E r X.Ψ x
  · rintro g ⟨b, hb, hgb⟩
    have hgx (τ : X.Ψ) : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat b τ :=
      congrFun hgb τ
    have hdiag (τ : X.Ψ) := _root_.GlobalTheory.upperTriangular_signForm_diagonal r (mat b τ) (fun a => sgn X.p0 a)
      (fun a => by unfold sgn; split_ifs <;> simp) (isUnit_iff_ne_zero.2 (hb τ).1) (fun a c h => (hb τ).2 a c h) (by
        have h1 := gram_mul_of_preserves τ.1 X.Gm _ (mat x τ) ((g.2 τ).2)
        have hJ := hx τ
        rw [gram_eq] at hJ
        rw [hgx τ, gram_eq, gram_eq, transpose_mul, Matrix.map_mul] at h1
        rw [← hJ]; refine Eq.trans ?_ h1; simp only [Matrix.mul_assoc])
    have hbd (τ : X.Ψ) : mat b τ = diagonal fun a => mat b τ a a := by
      ext a c; by_cases h : a = c
      · subst h; simp
      · simp [diagonal_apply_ne _ h, (hdiag τ).1 a c h]
    have hdet (τ : X.Ψ) : ∏ a, mat b τ a a = 1 := by
      have h := congrArg Matrix.det (hgx τ)
      rw [det_mul, det_mul, (g.2 τ).1, one_mul, hbd τ, det_diagonal] at h
      exact (mul_left_cancel₀ (isUnit_det_of_isOrth hx τ).ne_zero (h.symm.trans (mul_one _).symm))
    choose φ hφ using fun τ : X.Ψ => _root_.GlobalTheory.TorusAngles.exists_angles_of_prod_eq_one r (fun a => mat b τ a a) (hdiag τ).2 (hdet τ)
    refine ⟨φ, Subtype.ext (funext fun τ => Units.ext ?_)⟩
    show ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) * (mat x τ)⁻¹
    have hD : (diagonal fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) = mat b τ := by
      rw [hbd τ]; congr 1; funext a; exact hφ τ a
    rw [hD, ← hgx τ, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]

end GlobalTheory.TorusFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGeneratorDivBaseUnitEqGeneric
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DivConst

theorem gs_const {R K : Type} [CommRing R] [CommRing K] (g : R →+* K) {X Y : Scheme.{0}} {q : X ⟶ Sp R}
    {p : Y ⟶ Sp K} {φ : Y ⟶ X} (w : φ ≫ q = p ≫ spMap g) (y : Y) (b : R) :
    gs φ y ⊤ (q.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) =
      gs p y ⊤ ((Scheme.ΓSpecIso (.of K)).inv.hom (g b)) := by
  have h₁ := congrArg (fun φ : Y ⟶ Sp R ↦ φ.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom b)) w
  have h₂ := congrArg (fun φ : CommRingCat.of R ⟶ Γ(Spec (.of K), ⊤) ↦ φ.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  rw [gs_eq φ y ⊤ trivial, gs_eq p y ⊤ trivial]
  exact congrArg (Y.presheaf.germ ⊤ y trivial).hom (h₁.trans (congrArg p.appTop.hom h₂.symm))

theorem exists_genPull_eq : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by
  intro R K _ _ _ X Y φ p w M c a b hab u hu H
  let β : Γ(X.left, ⊤)ˣ := Units.map (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toMonoidHom b
  refine ⟨⟨fun i => u.s i * (res le_top β)⁻¹⟩, fun i j => unit_ext fun x hx => ?_, ?_⟩
  · have e := congrArg (gm (𝟙 X.left) x (M.U i ⊓ M.U j)) (hu i j)
    simp only [map_mul, map_inv] at e ⊢
    rw [e, gm_res _ x _ hx (res le_top β), gm_res _ x _ hx (res le_top β), gm_res _ x _ hx.1 β,
      gm_res _ x _ hx.2 β, mul_assoc]
  · obtain ⟨s⟩ := c
    refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
    have hy' : φ y ∈ M.U (j PUnit.unit) := mem_pull.1 hy
    refine (gm_res _ y _ hy _).trans ((gm_pull (𝟙 Y) φ y _ hy' _).trans ?_)
    have e := H (j PUnit.unit) Y (𝟙 Y) y hy'
    have e' : (gm (𝟙 Y ≫ φ) y ⊤ β).val = gs (𝟙 Y ≫ p) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
      rw [← gs_unit _ y ⊤ trivial, ← hab, Category.id_comp, Category.id_comp]
      exact gs_const _ w y b
    rw [← e', ← Units.val_mul] at e
    rw [map_mul, map_inv, gm_res (𝟙 Y ≫ φ) y _ hy' β, Units.ext e, mul_inv_cancel_comm]
    rfl

end GlobalTheory.DivConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveCochainModelTrivialProjectiveBund
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace GlobalTheory.EtC

theorem inv_fibQ (q N : ℕ) : Inv q (fibQ q N) := fun U ⟨x⟩ =>
  (show (invP q).obj (op U) from Sx.map (pullback.fst (trivV N (disc.obj (invP q))) (PGL.pr N)) x).down

theorem inv_pullback_disc (q N : ℕ) (F : PSh) (hF : Inv q (disc.obj F)) :
    Inv q (pullback (trivV N (disc.obj F)) (PGL.pr N)) := fun U ⟨x⟩ =>
  hF U ⟨Sx.map (pullback.fst (trivV N (disc.obj F)) (PGL.pr N)) x⟩

section
variable {q : ℕ}

theorem ev_comp_cochain {E : Spc} {I K : Cx (ZMod q)} {n d w : ℤ} (α : Cochain ((chains (ZMod q)).obj E) I n)
    (ψ : Cochain I K d) (h : n + d = w) (p : ℕ) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + w = t)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (α.comp ψ h) p t ht U x = Sec.map (ψ.v s t (by omega)) (ev (R := ZMod q) α p s hs U x) := by
  rw [ev_def, ev_def, Cochain.comp_v α ψ h _ s t hs (by omega)]
  rfl

theorem cast_cocycle {E : Spc} {n n' i i' : ℤ} (hn : n' = n) (hi : i' = i)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i')) n') :
    ∃ γ' : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n,
      (CohomologyClass.mk γ' : Ht q E n i) = Ht.cast hn hi (CohomologyClass.mk γ) ∧
      ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + n = s) (V : Scheme.{0}) (w : Sx E k V),
        ev (R := ZMod q) γ'.1 k s hs V w = twCast hi (ev (R := ZMod q) γ.1 k s (by omega) V w) := by
  subst hn hi
  exact ⟨γ, rfl, fun _ _ _ _ _ => rfl⟩

theorem sxmap_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    Sx.map g (Sx.map f x) = Sx.map (f ≫ g) x := rfl

theorem coe_cocycle_sum {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle K L n) :
    ((∑ j ∈ t, c j : Cocycle K L n) : Cochain K L n) = ∑ j ∈ t, (c j : Cochain K L n) :=
  map_sum (AddMonoidHom.mk' (fun c : Cocycle K L n => (c : Cochain K L n)) (fun _ _ => rfl)) c t

theorem cochain_sum_v {K L : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain K L n) (p p' : ℤ)
    (h : p + n = p') : (∑ j ∈ t, c j).v p p' h = ∑ j ∈ t, (c j).v p p' h :=
  map_sum (AddMonoidHom.mk' (fun c : Cochain K L n => c.v p p' h) (fun a b => Cochain.add_v a b p p' h)) c t

theorem Jsec_sum {N : ℕ} {I : Cx (ZMod q)} {n : ℤ} {U : Scheme.{0}} {ι : Type} (t : Finset ι)
    (c : ι → Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) I n) : Jsec (∑ j ∈ t, c j) = ∑ j ∈ t, Jsec (c j) :=
  map_sum ((toSheafify Scheme.etaleTopology.{0} (cotPre (ZMod q) q N I n)).app (op U)).hom c t

theorem ev_cocycle_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cocycle ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (↑(∑ j ∈ t, c j) : Cochain _ _ _) p s h U x = ∑ j ∈ t, ev (R := ZMod q) (c j).1 p s h U x := by
  rw [coe_cocycle_sum]
  exact map_sum (evHom I n p s h U x) _ t

theorem ev_cochain_sum {E : Spc} {I : Cx (ZMod q)} {n : ℤ} {ι : Type} (t : Finset ι) (c : ι → Cochain ((chains (ZMod q)).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := ZMod q) (∑ j ∈ t, c j) p s h U x = ∑ j ∈ t, ev (R := ZMod q) (c j) p s h U x :=
  map_sum (evHom I n p s h U x) c t

end

theorem pbf_disc_model : ∀ (q : ℕ) [NeZero q] (N : ℕ) (i : ℤ), ∃ (J : Cx (ZMod q)) (ψ : ∀ j : Fin N, Cocycle (res (ZMod q) (tw q (i - (j : ℕ)))) J (2 * (j : ℕ))), J.IsStrictlyGE 0 ∧ (∀ n, CategoryTheory.Injective (J.X n)) ∧ ∀ F : PSh, Inv q (disc.obj F) → ∀ n : ℤ, ∃ e : CohomologyClass ((chains (ZMod q)).obj (disc.obj F)) J n ≃+ Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i, ∀ a : ∀ j : Fin N, Ht q (disc.obj F) (n - 2 * (j : ℕ)) (i - (j : ℕ)), e (∑ j, cpost _ (ψ j) (n - 2 * (j : ℕ)) n (by omega) (a j)) = pbfMap q (trivV N (disc.obj F)) n i a := by
  intro q _ N i
  have hz : ∀ j : Fin N, ∃ z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q ((j : ℕ) : ℤ)))
      (2 * ((j : ℕ) : ℤ)), CohomologyClass.mk z = cpow q (c1 q (lineQ q N)) (j : ℕ) :=
    fun j => (cpow q (c1 q (lineQ q N)) (j : ℕ)).mk_surjective
  choose z hz using hz
  have hψ := fun j : Fin N => GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing q N (i - (j : ℕ)) (j : ℕ) i (by ring) (j : ℕ) (z j)
  choose ψ hψ using hψ
  refine ⟨Jcx (ZMod q) q N (res (ZMod q) (tw q i)), ψ,
    GlobalTheory.T.projBundleModelCochainComplex_isStrictlyGE _ q N _ (inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)),
    GlobalTheory.T.injective_projBundleModelCochainComplex_X _ q N _ (fun m => inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X m))), ?_⟩
  intro F hF n
  obtain ⟨θ, hθ1, hθ2⟩ := GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre q N F hF
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.discrete_projBundleModel_cohomology_equiv_prod_fibre (ZMod q) q N (res (ZMod q) (tw q i)) F n
  let e₁ : Ht q (pullback (trivV N (disc.obj F)) (PGL.pr N)) n i ≃+ Ht q (disc.obj F ⨯ fibQ q N) n i :=
    { toFun := pull _ θ.hom _ _
      invFun := pull _ θ.inv _ _
      left_inv := fun x => by rw [← pull_comp, θ.inv_hom_id, pull_id]
      right_inv := fun x => by rw [← pull_comp, θ.hom_inv_id, pull_id]
      map_add' := map_add _ }
  refine ⟨e₀.trans e₁.symm, fun a => ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  change e₀ _ = pull _ θ.hom _ _ (pbfMap q (trivV N (disc.obj F)) n i a)
  rw [GlobalTheory.T.pullback_projBundleFormulaMap_of_factor GlobalTheory.T.cup_chern_kummer_pullback_naturality q (trivV N (disc.obj F)) (lineQ q N) θ.hom prod.fst prod.snd (inv_fibQ q N)
    (inv_pullback_disc q N F hF) hθ1 hθ2 n i a]
  have hα := fun j : Fin N => GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos (ZMod q) F (res (ZMod q) (tw q (i - (j : ℕ)))) (n - 2 * ((j : ℕ) : ℤ)) (a j)
  choose α hαa hα0 using hα
  have hγ := fun j : Fin N => GlobalTheory.T.cupProduct_discreteSpace_fibre_eq_pairing q N F (α j) (z j) (hα0 j)
  choose γ hγc hγv using hγ
  have hγ' := fun j : Fin N => cast_cocycle (q := q) (E := disc.obj F ⨯ fibQ q N)
    (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) (show i - ((j : ℕ) : ℤ) + ((j : ℕ) : ℤ) = i by ring) (γ j)
  choose γ' hγ'c hγ'v using hγ'
  let mkH : ∀ {K L : Cx (ZMod q)} {m : ℤ}, Cocycle K L m →+ CohomologyClass K L m :=
    fun {K L m} => AddMonoidHom.mk' CohomologyClass.mk CohomologyClass.mk_add
  have hL : (∑ j, cpost _ (ψ j) (n - 2 * ((j : ℕ) : ℤ)) n (by omega) (a j)) =
      CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show CohomologyClass.mk (∑ j, zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)) =
      mkH (∑ j, zcomp (α j) (ψ j) _) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hαa j]
    rfl
  have hR : (∑ j : Fin N, ((cup q (pull _ (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (a j))
      (pull _ (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _) _ _ (cpow q (c1 q (lineQ q N)) j))).cast (by ring) (by ring) :
        Ht q _ n i)) = CohomologyClass.mk (∑ j, γ' j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show CohomologyClass.mk (∑ j, γ' j) = mkH (∑ j, γ' j) from rfl, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = CohomologyClass.mk (γ' j)
    rw [hγ'c j, hγc j, hαa j, hz j]
  rw [hL, hR]
  apply he₀
  · intro p hp s h
    have key : ∀ j : Fin N, (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1.v
        (-(p : ℤ)) s h = 0 := fun j => by
      rw [show (zcomp (α j) (ψ j) (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring)).1 =
        (α j).1.comp (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) from rfl]
      rw [Cochain.comp_v _ _ _ _ (-(p : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) s rfl (by omega), hα0 j p hp _ rfl, zero_comp]
    rw [coe_cocycle_sum, cochain_sum_v]
    exact Finset.sum_eq_zero fun j _ => key j
  · intro U x
    have hc := fun j : Fin N => hψ j (n - 2 * ((j : ℕ) : ℤ)) n (by ring) U (ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x)
    choose c hc1 hc2 using hc
    refine ⟨∑ j, c j, ?_, ?_⟩
    · rw [ev_cocycle_sum, Jsec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hc1 j]
      exact ev_comp_cochain (α j).1 (ψ j).1 (show n - 2 * ((j : ℕ) : ℤ) + 2 * ((j : ℕ) : ℤ) = n by ring) 0 _ n (by simp) (by simp) U x
    · intro k s hs V y
      rw [ev_cochain_sum, ev_cocycle_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc2 j, hγ'v j, hγv j]
      have e2 : Sx.map (prod.snd : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) = Sx.map prod.snd y :=
        (sxmap_comp (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) prod.snd y).trans
          (by rw [prod.map_snd, Category.comp_id]; rfl)
      have e1 : (Sx.map (p := k) (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _)
          (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y) : F.obj (op V)) =
          F.map (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U).op x :=
        (sxmap_comp (E := disc.obj (yoneda.obj U) ⨯ fibQ q N) _ _ y).trans (by
          rw [prod.map_fst]
          rfl)
      have e3 : Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U)
          (ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) U x) =
          ev (R := ZMod q) (α j).1 0 (n - 2 * ((j : ℕ) : ℤ)) (by simp) V (show Sx (disc.obj F) 0 V from Sx.map (p := k)
            (prod.fst : disc.obj F ⨯ fibQ q N ⟶ _) (Sx.map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))) y)) :=
        (ev_res _ _ _ _ _ _).trans (congrArg _ e1.symm)
      rw [e2, e3]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrime
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubring
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.TorsorUnionDescent

theorem exists_stage_torsor : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T _ _ ι _ _ _ 𝒜 hA hU q hq E _ _ _ _ _ Q _ D₁ _ _ act₁ htor
  obtain ⟨i₀, E₀, _, _, hE₀, ⟨iso₀⟩⟩ := GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union T ι 𝒜 hA hU E

  let ι' := {k : ι // i₀ ≤ k}
  haveI : IsDirected ι' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  haveI : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  let 𝒜' : ι' → Subring T := fun k => 𝒜 k.1
  have hA' : Monotone 𝒜' := fun a b hab => hA hab
  have hU' : ∀ x : T, ∃ k : ι', x ∈ 𝒜' k := fun x => by
    obtain ⟨j, hj⟩ := hU x
    obtain ⟨c, hjc, hic⟩ := directed_of (· ≤ ·) j i₀
    exact ⟨⟨c, hic⟩, hA hjc hj⟩
  obtain ⟨Ek, _, _, _, _, _, e, h, he, hh, heh, hid, hcomp, hinj, hsurj⟩ :=
    GlobalTheory.T.directedSystem_etale_baseChange_polynomial T ι' 𝒜' hA' hU' ⟨i₀, le_rfl⟩ (fun k => k.2) E E₀ ⟨iso₀⟩
  have he' : ∀ k (a : 𝒜' k), e k (algebraMap (𝒜' k) (Ek k) a) = algebraMap T E a := by
    intro k a
    have := congrArg (fun φ => φ (Polynomial.C a)) (he k)
    simpa [IsScalarTower.algebraMap_apply (𝒜' k) (Polynomial (𝒜' k)) (Ek k),
      IsScalarTower.algebraMap_apply T (Polynomial T) E] using this
  have hnz : ∀ (S S' : Subring T) (φ : S →+* S'), (∀ a, (φ a : T) = a) →
      ∀ a ∈ nonZeroDivisors S, φ a ∈ nonZeroDivisors S' := by
    intro S S' φ hφ a ha
    refine mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext ?_))
    have := congrArg Subtype.val h0
    rw [hφ] at this
    exact this
  have hnzT : ∀ (S : Subring T), ∀ a ∈ nonZeroDivisors S, S.subtype a ∈ nonZeroDivisors T := by
    intro S a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext h0))
  let g : ∀ k : ι', GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) := fun k =>
    GlobalTheory.GenFibMap.genFibMap (𝒜' k).subtype (e k) (he' k) (hnzT _) (Q.comap (e k)) Q rfl
  have hQ : ∀ k l (hkl : k ≤ l), Q.comap (e k) = (Q.comap (e l)).comap (h k l hkl) := by
    intro k l hkl
    rw [Ideal.comap_comap]
    congr 1
    ext y
    exact (heh k l hkl y).symm
  let f : ∀ k l : ι', k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))) := fun k l hkl =>
    GlobalTheory.GenFibMap.genFibMap (Subring.inclusion (hA' hkl)) (h k l hkl) (hh k l hkl)
      (hnz _ _ _ (fun _ => rfl)) (Q.comap (e k)) (Q.comap (e l)) (hQ k l hkl)
  have hgc : ∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y)) := fun k y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  have hfc : ∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y)) := fun k l hkl y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_torsor_model_filtered_colimit ι'
    (fun k => GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) f
    (fun k hkk => GlobalTheory.GenFibMap.genFibMap_id _ _ _ _ _ _ (hid k hkk))
    (fun k l m hkl hlm => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hcomp k l m hkl hlm (hkl.trans hlm)))
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) g
    (fun k l hkl => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun y => (heh k l hkl y).symm))
    (GlobalTheory.T.genericFibreLocalization_directedUnion_surjective T ι' 𝒜' hA' hU' E Q Ek e h he' heh hsurj g hgc)
    (GlobalTheory.T.genericFibreLocalization_directedUnion_kernel T ι' 𝒜' hA' hU' E Q Ek e h he' hh heh hinj hsurj g hgc f hfc)
    q hq D₁ act₁ htor
  obtain ⟨Di, _, _, acti, htori, ⟨iso₂⟩⟩ := hk
  refine ⟨k.1, Ek k, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, e k, he k,
    g k, GlobalTheory.GenFibMap.genFibMap_comp_algebraMap _ _ _ _ _ _ _, Di, inferInstance, inferInstance, acti, htori, ?_⟩
  intro C _ ψ σ hσ
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
      (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := (g k).toAlgebra
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) C :=
    (ψ.comp (g k)).toAlgebra
  let ψa : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k)
      (Localization.AtPrime (Q.comap (e k)))] C := { ψ with commutes' := fun r => rfl }
  let σa : Di →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))] C :=
    { σ with commutes' := fun r => (congrArg (fun φ => φ r) hσ : _) }
  refine ⟨(Algebra.TensorProduct.lift ψa σa (fun _ _ => Commute.all _ _)).toRingHom.comp
    iso₂.symm.toAlgHom.toRingHom, ?_⟩
  ext b
  simp [ψa]

end GlobalTheory.TorsorUnionDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExpStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  first | exact @GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | exact GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | (intros; apply GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierProdSingleCoordinateFunctionsStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  first | exact @GlobalTheory.fourier_prod_coord_complex | exact GlobalTheory.fourier_prod_coord_complex | (intros; apply GlobalTheory.fourier_prod_coord_complex <;> assumption)
end

