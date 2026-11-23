module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_mul {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a * b) = valF x U a * valF x U b := by
  simp only [valF, dif_pos h, map_mul]

theorem valF_mul_inv {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valF x U a.val * valF x U (a⁻¹).val = 1 := by
  rw [← valF_mul h, a.mul_inv]
  simp only [valF, dif_pos h, map_one]

theorem valF_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* F) (s : Γ(X, V)) :
    valF (spMap χ ≫ hV.fromSpec) V s = χ s := by
  have h0 : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V := fun q _ => h0 (Set.mem_univ (spMap χ q))
  rw [valF, dif_pos h]
  have e : (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom χ := by
    have e1 : hV.fromSpec.appLE V ⊤ h0 = (Scheme.ΓSpecIso Γ(X, V)).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, V)).presheaf.map_id _)).trans (Category.comp_id _)
    rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h0 le_rfl, e1, Category.assoc, Iso.inv_comp_eq]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  exact congrArg (fun g => g.hom s) e

theorem exists_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] (w : Sp R ⟶ X)
    (h : ⊤ ≤ w ⁻¹ᵁ V) : ∃ χ : Γ(X, V) →+* R, spMap χ ≫ hV.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hV.range_fromSpec]
    exact h (Set.mem_univ q)
  exact ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h')).hom,
    (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem le_of_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] {w : Sp R ⟶ X}
    {χ : Γ(X, V) →+* R} (h : spMap χ ≫ hV.fromSpec = w) : ⊤ ≤ w ⁻¹ᵁ V := fun q _ =>
  h ▸ hV.fromSpec_preimage_self.ge (Set.mem_univ (spMap χ q))

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

theorem frame_ind {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X} {u : Vecs Dw t k}
    (h : GlobalTheory.LocM.IsFrame t f x u) (τ : E →+* ℂ) : Ind t x (u τ) := by
  refine ⟨fun i => (h.1 τ i).1, fun cf cf' w h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := exists_tan fun i => (h.1 τ i).1
  have e := (comb_iff U cf w).1 (hU ▸ h1)
  refine (h.2 τ w (e ▸ isTan_tv _) fun a => ?_).unique h1 h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, eig_iff, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, (eig_iff (U i) a _).1 (congrFun hU i ▸ (h.1 τ i).2 a)]

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

theorem comb_push {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin m → R) :
    IsCombAtG t x (fun i => u i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pushE mu x' hx (tanOf (hu i))) cf (pushE mu x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

theorem frame_push {f' : c'.F →+* R} {f : c.F →+* R} (hf : ∀ τ a, f (embK c τ a) = f' (embK c' τ a))
    {u : Vecs Dw t' R} (h : GlobalTheory.LocM.IsFrame t' f' x' u) : GlobalTheory.LocM.IsFrame (Dw := Dw) t f x fun τ i => u τ i ≫ mu.φ := by
  refine ⟨fun τ i => ⟨isTan_push mu x' hx (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2, hf, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x' hx).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => (h.1 τ i).1) (isTan_tv v) cf).2
      (h.2 τ _ (isTan_tv v) fun a => (eig_iff v a _).2 ((pushE mu x' hx).injective ?_))
    rw [pushE_act, map_smul, ← hf]
    exact (eig_iff _ a _).1 (he a)

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem chart_frame (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) ((Z.fr a).bc φ) := by
  rw [← h, Category.assoc]
  exact _root_.GlobalTheory.ShFam.Pad.isFrame_baseChange E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    w ≫ Z.π ≫ (Y Z.i).s = spMap (φ.comp (Z.alg a)) ≫ spMap (Z.i.c.V W).subtype := by
  rw [Z.π_s, ← h, Category.assoc, Z.alg_s, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, RingHom.comp_assoc]

theorem range_opn (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) : Set.range w ⊆ Z.opn := by
  rintro _ ⟨q, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_of_fromSpec (Z.U a).2 h (Set.mem_univ q)⟩

theorem exists_open_lift (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp R ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π := by
  have := (Y Z.i).jQ_open
  let q : Sp R ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) _ ((Category.assoc _ _ _).trans (affineOpenChart_comp_structure_eq_spMap Z h))
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z h ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  exact ⟨IsOpenImmersion.lift _ q hr, by rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, IsOpenImmersion.lift_fac_assoc, hq]⟩

theorem tri_of_sameFlag {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {u u' : Vecs Dw t k}
    {ty : (E →+* ℂ) → Finset ℕ} (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ ty τ) (h : SameFlag ty t x u u') (τ : E →+* ℂ) :
    Tri t x (u τ) (u' τ) := fun j => h τ (j + 1) (hty τ _ j.2) j (Nat.lt_succ_self _)

theorem chart_tri (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {k : Type} [Field k] {a a' : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} {φ' : Γ(Z.X, (Z.U a').1) →+* k} {w : Sp k ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w)
    (h' : spMap φ' ≫ Z.chart a' = w) (τ : E →+* ℂ) :
    Tri (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ τ) ((Z.fr a').bc φ' τ) := by
  have := tri_of_sameFlag hty (Z.glue k a a' φ φ' (h.trans h'.symm)) τ
  rwa [← Category.assoc, h] at this

theorem isReduced_model (Z : Mdl Y i₀) : IsReduced Z.X :=
  have := Z.normal
  inferInstance

theorem isSeparated_base (i : Idx H p) : (Y i).X.IsSeparated := by
  have := projProper _ _ _ (Y i).proj
  exact ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩

theorem ext_unique (i : Idx H p) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ (Y i).X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have := isSeparated_base (Y := Y) i
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

end Models

section Bundle

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

end Bundle

section Main

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

variable (hf : IsMap Z' Z f) {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)
  (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) (M : LineModel Z b st x)

include hf hT hty



end Main

end GlobalTheory.ShFam.Pad.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthPolynomialRepresentation
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RepBound

theorem poly_bound {σ : Type} (P : MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ‖aeval x P‖ ≤ C * B ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖(a : ℂ)‖, 0, norm_nonneg _, fun B _ x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    obtain ⟨C2, d2, h2, hq⟩ := hq
    refine ⟨C1 + C2, d1 + d2, by positivity, fun B hB x hx => ?_⟩
    rw [map_add (f := _)]
    have e1 : B ^ d1 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    have e2 : B ^ d2 ≤ B ^ (d1 + d2) := pow_le_pow_right₀ hB (by omega)
    calc ‖aeval x p + aeval x q‖ ≤ ‖aeval x p‖ + ‖aeval x q‖ := norm_add_le _ _
      _ ≤ C1 * B ^ d1 + C2 * B ^ d2 := add_le_add (hp B hB x hx) (hq B hB x hx)
      _ ≤ C1 * B ^ (d1 + d2) + C2 * B ^ (d1 + d2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 h1) (mul_le_mul_of_nonneg_left e2 h2)
      _ = (C1 + C2) * B ^ (d1 + d2) := by ring
  | mul_X p s hp =>
    obtain ⟨C1, d1, h1, hp⟩ := hp
    refine ⟨C1, d1 + 1, h1, fun B hB x hx => ?_⟩
    rw [map_mul, aeval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hp B hB x hx) (hx s) (norm_nonneg _)
      (mul_nonneg h1 (pow_nonneg (by linarith) _))

theorem poly_bound_fam {κ σ : Type} [Fintype κ] (P : κ → MvPolynomial σ ℤ) : ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
    ∀ (B : ℝ), 1 ≤ B → ∀ x : σ → ℂ, (∀ s, ‖x s‖ ≤ B) → ∀ k, ‖aeval x (P k)‖ ≤ C * B ^ d := by
  choose C d hC h using fun k => poly_bound (P k)
  refine ⟨∑ k, C k, ∑ k, d k, Finset.sum_nonneg fun k _ => hC k, fun B hB x hx k => ?_⟩
  exact (h k B hB x hx).trans (mul_le_mul
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ k))
    (pow_le_pow_right₀ hB (Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ k)))
    (pow_nonneg (by linarith) _) (Finset.sum_nonneg fun k _ => hC k))

variable {ι : Type} {m : ι → ℕ}

def adjPoly (m : ι → ℕ) (w : EntIx m) : MvPolynomial (EntIx m) ℤ :=
  Matrix.adjugate (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)) w.2.1 w.2.2

theorem aeval_adjPoly (A : Mat m ℂ) (w : EntIx m) :
    aeval (fun u : EntIx m => A u.1 u.2.1 u.2.2) (adjPoly m w) = (A w.1).adjugate w.2.1 w.2.2 := by
  have e : (Matrix.of fun p q : Fin (m w.1) => (X ⟨w.1, (p, q)⟩ : MvPolynomial (EntIx m) ℤ)).map
      (aeval fun u : EntIx m => A u.1 u.2.1 u.2.2) = A w.1 := by
    ext p q; simp
  rw [← e]
  exact congrFun (congrFun (RingHom.map_adjugate (aeval (R := ℤ) fun u : EntIx m => A u.1 u.2.1 u.2.2).toRingHom _) w.2.1) w.2.2

variable [Fintype ι]

def lieCoeff (ρ : PolyRep m) (i j : Fin ρ.M) (w : EntIx m) : ℂ :=
  aeval (fun u : EntIx m => (1 : Mat m ℂ) u.1 u.2.1 u.2.2) (pderiv w (ρ.ent i j))

theorem lie_apply (ρ : PolyRep m) (A : Mat m ℂ) (i j : Fin ρ.M) :
    ρ.lie A i j = ∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2 := rfl

def lieNorm (ρ : PolyRep m) : ℝ := ∑ i, ∑ j, ∑ w, ‖lieCoeff ρ i j w‖

theorem lieNorm_nonneg (ρ : PolyRep m) : 0 ≤ lieNorm ρ := by unfold lieNorm; positivity

theorem norm_lie_mul_le (ρ : PolyRep m) (A : Mat m ℂ) {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ w : EntIx m, ‖A w.1 w.2.1 w.2.2‖ * t ≤ c) (i j : Fin ρ.M) :
    ‖ρ.lie A i j‖ * t ≤ lieNorm ρ * |c| := by
  have h1 : ‖ρ.lie A i j‖ * t ≤ ∑ w, ‖lieCoeff ρ i j w‖ * |c| := by
    rw [lie_apply]
    calc ‖∑ w, lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖ * t
        ≤ (∑ w, ‖lieCoeff ρ i j w * A w.1 w.2.1 w.2.2‖) * t :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht
      _ = ∑ w, ‖lieCoeff ρ i j w‖ * (‖A w.1 w.2.1 w.2.2‖ * t) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun w _ => ?_; rw [norm_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left ((h w).trans (le_abs_self c)) (norm_nonneg _)
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg c)
  unfold lieNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖lieCoeff ρ i j w‖)
    (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ∑ w, ‖lieCoeff ρ i j w‖) (fun j _ => by positivity)
    (Finset.mem_univ j)

theorem lie_neg (ρ : PolyRep m) (A : Mat m ℂ) : ρ.lie (fun τ => -A τ) = -ρ.lie A := by
  ext i j; simp [lie_apply, Finset.sum_neg_distrib]

theorem lie_sub (ρ : PolyRep m) (A B : Mat m ℂ) : ρ.lie (fun τ => A τ - B τ) = ρ.lie A - ρ.lie B := by
  ext i j; simp [lie_apply, mul_sub, Finset.sum_sub_distrib]

theorem mdel_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdel (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdel (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdel_apply, lie_apply]
  rw [del_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [del_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem mdbar_lie (ρ : PolyRep m) {n : ℕ} {A : V n → Mat m ℂ} {v : V n}
    (h : ∀ τ, MContDiffAt 1 (fun u => A u τ) v) (ξ : V n) :
    mdbar (fun u => ρ.lie (A u)) v ξ = ρ.lie (fun τ => mdbar (fun u => A u τ) v ξ) := by
  ext i j
  simp only [mdbar_apply, lie_apply]
  rw [dbar_sum (fun w _ => (differentiableAt_const _).mul ((h w.1).diff w.2.1 w.2.2)),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h w.1).diff w.2.1 w.2.2)]
  simp

theorem poinWt_nonneg {n : ℕ} (S : Finset (Fin n)) (v : V n) (a : Fin n) : 0 ≤ poinWt S v a := by
  unfold poinWt; split_ifs <;> positivity

end GlobalTheory.RepBound

namespace GlobalTheory.RepBound

theorem le_mul_pow_of_le {x K c' L : ℝ} {e N' : ℕ} (hx : x ≤ K * L ^ e) (hK : K ≤ c') (hK0 : 0 ≤ K)
    (hL : 1 ≤ L) (he : e ≤ N') : x ≤ c' * L ^ N' :=
  hx.trans (mul_le_mul hK (pow_le_pow_right₀ hL he) (pow_nonneg (by linarith) _) (hK0.trans hK))

theorem goodBound_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ),
    ∀ (n : ℕ) (S : Finset (Fin n)) (G : V n → Mat m ℂ) (v : V n), (∀ τ, MContDiffAt 2 (fun u => G u τ) v) →
      (∀ τ, (G v τ).det ≠ 0) → 1 ≤ ∑ a ∈ S, |Real.log ‖v a‖| → (∀ τ, GoodBound S c N (fun u => G u τ) v) →
        GoodBound S c' N' (fun u => ρ.ev (G u)) v := by
  intro ι _ m ρ c N
  obtain ⟨C1, d1, hC1, h1⟩ := poly_bound_fam (fun p : Fin ρ.M × Fin ρ.M => ρ.ent p.1 p.2)
  obtain ⟨C2, d2, hC2, h2⟩ := poly_bound ρ.ent.det
  obtain ⟨C3, d3, hC3, h3⟩ := poly_bound_fam (adjPoly m)
  have hc₁ : 1 ≤ max c 1 := le_max_right _ _
  have hc₀ : 0 ≤ max c 1 := by linarith
  have hK1 : 0 ≤ C1 * max c 1 ^ d1 := mul_nonneg hC1 (pow_nonneg hc₀ _)
  have hK2 : 0 ≤ C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) :=
    mul_nonneg (mul_nonneg hC2 (pow_nonneg (by linarith) _)) (pow_nonneg hc₀ _)
  have hK3 : 0 ≤ lieNorm ρ * |c| := mul_nonneg (lieNorm_nonneg ρ) (abs_nonneg c)
  refine ⟨C1 * max c 1 ^ d1 + C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2) + lieNorm ρ * |c|,
    N * d1 + N * ((d3 + 1) * d2), ?_⟩
  intro n S G v hG hdet hL hB
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := by linarith
  set B := max c 1 * L ^ N with hBdef
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hc₁ (one_le_pow₀ hL)
  have hx : ∀ w : EntIx m, ‖G v w.1 w.2.1 w.2.2‖ ≤ B := fun w =>
    ((hB w.1).entry w.2.1 w.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
  have hu : ∀ τ, IsUnit (G v τ).det := fun τ => isUnit_iff_ne_zero.2 (hdet τ)
  have hcv := (_root_.GlobalTheory.GoodMetric.conn_curvPoly_ev ι m ρ n G v hG hdet).1
  have hcvE : ∀ ξ, (fun u => conn (fun w => ρ.ev (G w)) u ξ) =ᶠ[𝓝 v]
      (fun u => ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) := fun ξ => hcv.mono fun u hu => hu ξ
  have hc1 : ∀ τ ξ, MContDiffAt 1 (fun u => conn (fun w => G w τ) u ξ) v :=
    fun τ ξ => (hG τ).conn (hu τ) (by norm_num) ξ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change ‖ρ.ev (G v) i j‖ ≤ _
    have := h1 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx (i, j)
    refine le_mul_pow_of_le (K := C1 * max c 1 ^ d1) (e := N * d1) ?_ (by linarith) hK1 hL (by omega)
    refine this.trans_eq ?_
    rw [hBdef, mul_pow, ← pow_mul]; ring
  · change ‖(ρ.ev (G v)).det‖⁻¹ ≤ _
    set Gi : Mat m ℂ := fun τ => (G v τ)⁻¹ with hGi
    have hmul : ρ.ev (G v) * ρ.ev Gi = 1 := by
      have e : G v * Gi = 1 := funext fun τ => Matrix.mul_nonsing_inv _ (hu τ)
      rw [PolyRep.ev, PolyRep.ev, ← ρ.mul ℂ, e]
      exact ρ.one ℂ
    have hdm : (ρ.ev (G v)).det * (ρ.ev Gi).det = 1 := by rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hinv : ‖(ρ.ev (G v)).det‖⁻¹ = ‖(ρ.ev Gi).det‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right hdm]
    have hpoly : (ρ.ev Gi).det = aeval (fun w : EntIx m => Gi w.1 w.2.1 w.2.2) ρ.ent.det :=
      (AlgHom.map_det _ _).symm
    have hy : ∀ w : EntIx m, ‖Gi w.1 w.2.1 w.2.2‖ ≤ (C3 + 1) * B ^ (d3 + 1) := by
      intro w
      have ha := h3 B hB1 (fun w : EntIx m => G v w.1 w.2.1 w.2.2) hx w
      rw [aeval_adjPoly (G v) w] at ha
      have hd : ‖(G v w.1).det‖⁻¹ ≤ B :=
        ((hB w.1).det).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL0 _))
      have e : Gi w.1 w.2.1 w.2.2 = ((G v w.1).det)⁻¹ * (G v w.1).adjugate w.2.1 w.2.2 := by
        simp [hGi, Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e, norm_mul, norm_inv]
      have hBd : 0 ≤ B ^ d3 := pow_nonneg (by linarith) _
      calc ‖(G v w.1).det‖⁻¹ * ‖(G v w.1).adjugate w.2.1 w.2.2‖ ≤ B * (C3 * B ^ d3) :=
            mul_le_mul hd ha (norm_nonneg _) (by linarith)
        _ ≤ (C3 + 1) * B ^ (d3 + 1) := by
            rw [pow_succ]; nlinarith [mul_nonneg hBd (by linarith : (0:ℝ) ≤ B)]
    have hB2 : 1 ≤ (C3 + 1) * B ^ (d3 + 1) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hB1)
    have hd2 := h2 _ hB2 _ hy
    rw [hinv, hpoly]
    refine le_mul_pow_of_le (K := C2 * (C3 + 1) ^ d2 * max c 1 ^ ((d3 + 1) * d2))
      (e := N * ((d3 + 1) * d2)) ?_ (by linarith) hK2 hL (by omega)
    refine hd2.trans_eq ?_
    rw [hBdef, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  · intro a i j
    change ‖conn (fun u => ρ.ev (G u)) v (coordVec a) i j‖ * poinWt S v a ≤ _
    have e := (hcvE (coordVec a)).self_of_nhds
    simp only at e
    rw [e]
    exact (norm_lie_mul_le ρ _ (poinWt_nonneg S v a) (fun w => (hB w.1).form a w.2.1 w.2.2) i j).trans
      (by linarith)
  · intro a b i j
    have e : curv (fun u => ρ.ev (G u)) v (coordVec a) (coordVec b) =
        ρ.lie (fun τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)) := by
      rw [curv, mdbar_congr (hcvE (coordVec a)), mdbar_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_neg]
      rfl
    rw [e]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).dbar a b w.2.1 w.2.2) i j).trans (by linarith)
  · intro a b i j
    rw [mdel_congr (hcvE (coordVec b)), mdel_congr (hcvE (coordVec a)),
      mdel_lie ρ (fun τ => hc1 τ (coordVec b)), mdel_lie ρ (fun τ => hc1 τ (coordVec a)), ← lie_sub]
    exact (norm_lie_mul_le ρ _ (mul_nonneg (poinWt_nonneg S v a) (poinWt_nonneg S v b))
      (fun w => (hB w.1).del a b w.2.1 w.2.2) i j).trans (by linarith)

end GlobalTheory.RepBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LineNorm

end GlobalTheory.LineNorm

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LineNorm

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.LineNorm
end
end

