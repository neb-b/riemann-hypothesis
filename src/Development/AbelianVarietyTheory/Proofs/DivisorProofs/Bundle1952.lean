module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulHorizontalDetLieCoordinate
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.HorConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_matrix {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {m n : ℕ} (h : m = n)
    {v v' : Fin n → (epsAt x ⟶ t.G)} {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k)
    (hv' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v' i).left = u' k)
    {M : Matrix (Fin m) (Fin m) R} (hM : ∀ i, IsCombAtG t x u (M i) (u' i)) :
    ∃ M' : Matrix (Fin n) (Fin n) R, M'.det = M.det ∧ ∀ i, IsCombAt x (M' i) v (v' i) := by
  subst h
  refine ⟨M, rfl, fun i => (EigParts.comb_iff v _ _).2 ?_⟩
  rw [hv' i i rfl, show (fun i => (v i).left) = u from funext fun i => hv i i rfl]
  exact hM i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}


open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq in
theorem exists_matrix_det_ne {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Y.X} (f₁ f₂ : EigFrame Y φ x)
    (ρ : E →+* ℂ) : ∃ M : Matrix (Fin (D.mult ρ)) (Fin (D.mult ρ)) k,
      (∀ i, IsCombAtG Y.t x (f₁.v ρ) (M i) (f₂.v ρ i)) ∧ M.det ≠ 0 := by
  obtain ⟨n, xc, hx⟩ := exists_chart Y.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan ρ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan ρ i)
  choose M hM using fun i => (f₁.basis ρ _ (f₂.tan ρ i) (f₂.eig ρ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v ρ = fun j => vec Y.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  have hind : ∀ a : Fin (D.mult ρ) → k, ∑ i, a i • e₂ i = 0 → a = 0 := fun a ha => by
    have hb := f₂.basis ρ _ (vec_tan hx 0) ((vec_eig_iff hx _ _).2 (Submodule.zero_mem _))
    rw [show f₂.v ρ = fun j => vec Y.t _ xc (e₂ j) from funext he₂] at hb
    exact hb.unique ((comb_iff hx _ _ _).2 ha.symm) ((comb_iff hx _ _ _).2 (by simp))
  refine ⟨Matrix.of M, hM, fun h0 => ?_⟩
  obtain ⟨a, ha, ha0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine ha (hind a ?_)
  simp only [hM', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.sum_smul]
  have : ∑ i, a i * M i j = 0 := congrFun ha0 j
  rw [this, zero_smul]

theorem quot_eq {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {e : c.F →+* ℂ} {h : CxFr Y e → ℂ} (hh : HorFn τ h)
    {V : Set (gen Y)} {σb : RuleY Y} (hσ : SecY Y V τ σb) (a a' : CxFr Y e) (ha : a.1.1 = a'.1.1) (hi : Inner a.1)
    {v w v' w'} (hf : FrY Y V τ e a.1.1 v w) (hm : Match τ a.2 v w) (hf' : FrY Y V τ e a'.1.1 v' w')
    (hm' : Match τ a'.2 v' w') : σb ℂ a.1.1 v w * (h a)⁻¹ = σb ℂ a'.1.1 v' w' * (h a')⁻¹ := by
  obtain ⟨x, f⟩ := a
  obtain ⟨x', f'⟩ := a'
  obtain rfl : x = x' := Subtype.ext ha
  obtain ⟨M, hM, hM0⟩ := exists_matrix_det_ne f f' τ
  obtain ⟨N, hN, -⟩ := exists_matrix_det_ne f f' (conjEmb τ)
  obtain ⟨M', eM, hM'⟩ := exists_matrix (GlobalTheory.Harm.mult_of_mem D hτ) hm.1 hm'.1 hM
  obtain ⟨N', eN, hN'⟩ := exists_matrix (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) hm.2 hm'.2 hN
  have e₁ := hσ.2 ℂ e x.1 v w v' w' M' N' hf hf' hM' hN'
  have e₂ := hh.2.1 ⟨x, f⟩ ⟨x, f'⟩ M N hi ⟨rfl, hM⟩ ⟨rfl, hN⟩
  have h₁ := hh.1 ⟨x, f⟩ hi
  have h₂ := hh.1 ⟨x, f'⟩ hi
  rw [eM, eN] at e₁
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂]
  refine mul_right_cancel₀ hM0 ?_
  linear_combination σb ℂ x.1 v w * e₂ + h ⟨x, f⟩ * e₁


open GlobalTheory.CxPts GlobalTheory.ShFam.Hor.Sec in
theorem exists_const_mul_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hstr hτ hh σb hσ
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hstr
  choose v₀ w₀ hf₀ hm₀ using fun y => (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) _ (hφ y)
    (by rintro _ ⟨z, rfl⟩; rw [← hV, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩) (fr y)).1
  let s (y : B.X) : Γ(B.X, W y) := σb _ _ (v₀ y) (w₀ y)
  have key (y) (p : GlobalTheory.CxPts B.str e) (hp : p ∈ ptsIn B.str e (W y)) :
      ∃ v w, FrY Y V τ e (a y p).1.1 v w ∧ Match τ (a y p).2 v w ∧ σb ℂ (a y p).1.1 v w = ev B.str e _ (s y) p := by
    have hx : (a y p).1.1 = spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io := by
      have : spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) = p.1 :=
        GlobalTheory.Points.specMap_valMap_fromSpec (hW y) p.1 hp
      rw [ha, ← Category.assoc, this]
    obtain ⟨v, w, h₁, h₂, h₃⟩ := exists_pull (evHom hp) (hf₀ y) hx
    have hj : (evHom hp).comp (φ y) = e :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective (h₁.1.symm.trans (a y p).1.2))
    refine ⟨v, w, by have := h₁; rwa [hj] at this, ⟨fun i k hik => ?_, fun i k hik => ?_⟩, ?_⟩
    · rw [h₂, (hm₀ y).1 i k hik, hv y p hp]
    · rw [h₃, (hm₀ y).2 i k hik, hv y p hp]
    · rw [ev_eq hp]
      exact hσ.1 _ ℂ (evHom hp) (Chart.dualMapR (evHom hp)) _ _ _ _ _ _ v w
        (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
        (by ext <;> simp [Chart.dualMapR]) (hf₀ y) h₁ hx h₂ h₃
  have hA : Dense (ptsIn B.str e (io ⁻¹ᵁ (genBd Y).compl)) := by
    refine (_root_.GlobalTheory.CxPtsDense.nonempty_and_dense c.F B e).2 _ ?_
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨z, fun hb => hb hz⟩
  let R := AnRead.all B.str e B.dim
  choose u hu he using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  let pt (z : GlobalTheory.CxPts B.str e) : B.X := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : GlobalTheory.CxPts B.str e) : z ∈ ptsIn B.str e (W (pt z)) := mem_ptsIn.2 (hy _)
  obtain ⟨q, hq, hqe⟩ := exists_holoOn_of_local (R := R) hA (S := Set.univ)
    (u := fun z => ev B.str e _ (s (pt z)) z * (h (a (pt z) z))⁻¹) fun y _ =>
    ⟨ptsIn B.str e (W (pt y)), fun z => ev B.str e _ (s (pt y)) z * u (pt y) z, isOpen_ptsIn _, hpt y,
      (R.holoOn_ev _ _).mul (hu _), fun z hz => by
        obtain ⟨v, w, h₁, h₂, h₃⟩ := key _ z hz.1
        obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
        have := quot_eq hτ hh hσ _ _ ((ha _ _).trans (ha _ _).symm) ((inner_iff (ha _ z)).2 hz.2) h₁ h₂ h₁' h₂'
        rw [h₃, h₃'] at this
        simp only [he _ hz]
        exact this⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.ConstFn.holoOn_univ_const c.F B e R q hq
  refine ⟨κ, fun b v w hi hb hm => ?_⟩
  have hr : Set.range b.1.1 ⊆ Set.range io := hV ▸ hb.2.1
  have hl : IsOpenImmersion.lift io b.1.1 hr ≫ io = b.1.1 := IsOpenImmersion.lift_fac _ _ _
  let z : GlobalTheory.CxPts B.str e := ⟨IsOpenImmersion.lift io b.1.1 hr, by rw [← hstr, ← Category.assoc, hl]; exact b.1.2⟩
  obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
  have e₁ := quot_eq hτ hh hσ b _ (hl.symm.trans (ha _ z).symm) hi hb hm h₁' h₂'
  have e₂ := hqe (x := z) ⟨trivial, (inner_iff hl.symm).1 hi⟩
  rw [hκ] at e₂
  rw [h₃'] at e₁
  rw [e₂]
  exact (mul_inv_eq_iff_eq_mul₀ (hh.1 b hi)).1 e₁

end GlobalTheory.DetLine.HorConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
section
open GlobalTheory.SiegelTor Polynomial

namespace GlobalTheory.SiegelTor

theorem isPrimitiveRoot_zetaAway {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaAway N) N :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway N).subtype) (Complex.isPrimitiveRoot_exp N hN) Subtype.val_injective

theorem cycAway_hom_ext {N : ℕ} (hN : N ≠ 0) {R : Type*} [CommRing R] {β β' : cycAway N →+* R}
    (h : β (zetaAway N) = β' (zetaAway N)) : β = β' := by
  ext ⟨x, hx⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
        Subtype.ext (by simpa using mul_inv_cancel₀ hN')
      have e₁ := congrArg β e
      have e₂ := congrArg β' e
      rw [map_mul, map_natCast, map_one] at e₁ e₂
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact e₁) e₂
  | zero => exact (map_zero β).trans (map_zero β').symm
  | one => exact (map_one β).trans (map_one β').symm
  | add x y hx hy ihx ihy =>
    exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg _ ih).trans (map_neg β' ⟨x, hx⟩).symm)
  | mul x y hx hy ihx ihy =>
    exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)

theorem exists_cycAway_hom_complex {N : ℕ} (hN : N ≠ 0) {μ : ℂ} (hμ : IsPrimitiveRoot μ N) :
    ∃ f : cycAway N →+* ℂ, f (zetaAway N) = μ := by
  have hp := Nat.pos_of_ne_zero hN
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  have hi : IsIntegral ℚ (zetaAway N : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway N : ℂ)}
  have hle : cycAway N ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K N)
  have hr : μ ∈ (minpoly ℚ (zetaAway N : ℂ)).aroots ℂ := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero N ℚ, ?_⟩
    rw [cyclotomic_eq_minpoly_rat hμ hp]
    exact minpoly.aeval ℚ μ
  let g : K →ₐ[ℚ] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨μ, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway N : ℂ)) = μ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨μ, hr⟩
  exact ⟨g.toRingHom.comp (Subring.inclusion hle), hg⟩

theorem exists_cycAway_end {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ f : cycAway N →+* cycAway N, f (zetaAway N) = zetaAway N ^ m := by
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  obtain ⟨f, hf⟩ := exists_cycAway_hom_complex hN (hz.pow_of_coprime m hm)
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : ∀ x, f x ∈ cycAway N := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hf ▸ pow_mem (zetaAway N).2 m
      · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ hN')
        have e₁ := congrArg f e
        rw [map_mul, map_natCast, map_one] at e₁
        exact Set.mem_of_eq_of_mem (eq_inv_of_mul_eq_one_right e₁) (Subring.subset_closure (Or.inr rfl))
    | zero => exact Set.mem_of_eq_of_mem (map_zero f) (zero_mem (cycAway N))
    | one => exact Set.mem_of_eq_of_mem (map_one f) (one_mem (cycAway N))
    | add x y hx hy ihx ihy => exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  exact ⟨f.codRestrict (cycAway N) hmem, Subtype.ext hf⟩

theorem exists_cycAway_aut {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m := by
  have hz := isPrimitiveRoot_zetaAway hN
  have : NeZero N := ⟨hN⟩
  obtain ⟨k, -, hk⟩ := (hz.pow_of_coprime m hm).eq_pow_of_pow_eq_one hz.pow_eq_one
  have hkc : k.Coprime N := by
    rw [← (hz.pow_of_coprime m hm).pow_iff_coprime (Nat.pos_of_ne_zero hN), hk]; exact hz
  obtain ⟨f, hf⟩ := exists_cycAway_end hN hm
  obtain ⟨g, hg⟩ := exists_cycAway_end hN hkc
  refine ⟨RingEquiv.ofRingHom f g (cycAway_hom_ext hN ?_) (cycAway_hom_ext hN ?_), hf⟩
  · rw [RingHom.comp_apply, hg, map_pow, hf, hk, RingHom.id_apply]
  · rw [RingHom.comp_apply, hf, map_pow, hg, ← pow_mul, mul_comm, pow_mul, hk, RingHom.id_apply]

theorem exists_pow_of_isLocalRing {N : ℕ} (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R]
    (β β' : cycAway N →+* R) : ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m := by
  classical
  have hp := Nat.pos_of_ne_zero hN
  have : NeZero N := ⟨hN⟩
  have hz := isPrimitiveRoot_zetaAway hN
  have h₁ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β)
  have h₂ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β')
  obtain ⟨i, hi, he⟩ := h₁.eq_pow_of_pow_eq_one h₂.pow_eq_one
  refine ⟨i, by rw [← h₁.pow_iff_coprime hp, he]; exact h₂, ?_⟩
  have hprod : ∏ k ∈ Finset.range N, (β' (zetaAway N) - β (zetaAway N) ^ k) = 0 := by
    have e := congrArg (fun p => (p.map β).eval (β' (zetaAway N))) (X_pow_sub_C_eq_prod hz hp (one_pow N))
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_prod, eval_prod, eval_sub, eval_pow,
      eval_X, eval_C, mul_one, map_one, map_pow, Polynomial.map_one, eval_one] at e
    rw [← e, ← map_pow, hz.pow_eq_one, map_one, sub_self]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)] at hprod
  have hu : IsUnit (∏ k ∈ (Finset.range N).erase i, (β' (zetaAway N) - β (zetaAway N) ^ k)) := by
    refine IsUnit.prod_iff.2 fun k hk => ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, sub_ne_zero]
    intro h
    obtain ⟨hki, hk⟩ := Finset.mem_erase.1 hk
    exact hki (h₁.pow_inj (Finset.mem_range.1 hk) hi (h.symm.trans he.symm))
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 hprod)

theorem cycAway_galois : ∀ N : ℕ, N ≠ 0 → (∀ m : ℕ, m.Coprime N → ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m) ∧ (∀ (R : Type) [CommRing R] (β β' : cycAway N →+* R), β (zetaAway N) = β' (zetaAway N) → β = β') ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β β' : cycAway N →+* R), ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m :=
  fun _ hN => ⟨fun _ hm => exists_cycAway_aut hN hm, fun _ _ _ _ h => cycAway_hom_ext hN h,
    fun _ _ _ β β' => exists_pow_of_isLocalRing hN β β'⟩

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevel
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefEig

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem actLev_levB (p : PtAt ex Csz) (i : Fin D.R.m) :
    ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  exact ⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩


set_option maxHeartbeats 1000000 in
theorem mem_eigSub_iff (p : PtAt ex Csz) (i : Fin D.R.m) (χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (f : p.T.R ((i : ℕ) + 1)) :
    f ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      ∀ u : (p.F.lv2.lvl false).P,
        actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f := by
  simp only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  rfl


end GlobalTheory.DefEig
end

