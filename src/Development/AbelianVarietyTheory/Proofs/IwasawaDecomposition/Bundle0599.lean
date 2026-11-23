module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivision
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.OxMove

set_option linter.style.haveILetI false

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

section General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JW (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Type :=
  ∀ i : Fin D.R.m, (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

def wpW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (i : Fin D.R.m) (c : A3.fam3.base3.Ix) :
    Submodule D.what₂.LL (Fin ((R.toCx3 F).dW false i) → D.what₂.LL) := (by with_unfolding_all exact (((cxW R F u).WpK false i c) :))

def overW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F) (σ : D.what₂.FT) (c : A3.fam3.base3.Ix) : Prop :=
  ∀ i : Fin D.R.m, D.what₂.isot ((i : ℕ) + 1) σ ≤
    Submodule.span ℂ ((j i) '' (wpW R F u i c : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)))

def lamW (R : RealDat3 D A3 Ks) (F : Face3 D A3) (u : Parts R) (j : JW R F)
    (l : ℕ → D.what₂.FT → (D.what₂.LL →+* ℂ) → ℝ) : Prop :=
  ∃ lab : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, (∃ c, overW R F u j σ c) → overW R F u j σ (lab σ)) ∧
    ∀ (i : Fin D.R.m) (σ : D.what₂.FT) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
      (D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
        l ((i : ℕ) + 1) σ e = Real.log (R.lam3 i A3.A.μ0 (lab σ) (InfinitePlace.mk e))) ∧
      (D.what₂.isot ((i : ℕ) + 1) σ = ⊥ → l ((i : ℕ) + 1) σ e = 0)

end General

section Copy

variable {B : Base} {C : Cols B} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks]

abbrev mv (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Late B C := Db.setDivZ a N h


set_option maxHeartbeats 4000000 in
theorem lamAre_copy (a : Late B C) (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ)
    [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)
    {X0 : BaseLevelRowSide a.D} {Y : R3.Read (A3 := A) R.toRealDat F.lv2 X0} (Z : R3.ReadL R F X0 Y) (X : DivX a.D)
    (X' : DivX (mv a N h).D) (hX : HEq X'.logLam X.logLam) {X0' : BaseLevelRowSide (mv a N h).D} :
    letI := alg (mv a N h) iK
    ∀ {Y' : R3.Read (A3 := famInThreeCoefficientChange (mv a N h) A) (real3 (mv a N h) R).toRealDat (face3 (mv a N h) F).lv2 X0'}
      (Z' : R3.ReadL (real3 (mv a N h) R) (face3 (mv a N h) F) X0' Y'), HEq Z'.jW Z.jW → LamAre Z X → LamAre Z' X' := by
  letI := alg (mv a N h) iK
  intro Y' Z' hj hl
  have h1 : lamW R F (R.EEp3, R.toRealDat.EEat, R.Wp3) ((by with_unfolding_all exact (Z.jW :))) X.logLam := (by with_unfolding_all exact (hl :))
  have ej : ((by with_unfolding_all exact (Z.jW :)) : JW R F) = (by with_unfolding_all exact (Z'.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj.symm :)))
  have el : X.logLam = (by with_unfolding_all exact (X'.logLam :)) := eq_of_heq ((by with_unfolding_all exact (hX.symm :)))
  have h2 := cast (congr (congrArg₂ (lamW R F) (parts_eq (mv a N h) R F) ej) el) h1
  exact (by with_unfolding_all exact (h2 :))

end Copy


set_option maxHeartbeats 4000000 in
theorem oAt_setDiv : ∀ (Γ : GeoP) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (O : Obj2 (w.D Z)) (O' : Obj2 (w.D (Db.setDivZ Z N h))), O' = O.tr N h → ∀ (t : RowsT K w Z Wt O.p0) (t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0), R3.Rw.RowsSame t t' → OAt (geoCl Γ) t O.X → Nonempty (OAt (geoCl Γ) t' O'.X) := by
  intro Γ K B f T w Z Wt N h O O' hO t t' hs hp
  have hOX : O'.X = (by with_unfolding_all exact ((divTr (D := w.D Z) N h O.X) :)) := by subst hO; exact (by with_unfolding_all exact ((Eq.refl (divTr (D := w.D Z) N h O.X)) :))
  clear hO
  generalize O'.X = X' at hOX
  revert t'
  generalize O'.p0 = p0'
  intro t' hs
  subst hOX
  cases t' with | mk hX' r' => ?_
  cases r' with | mk z' holds' Y' Zr' => ?_
  cases z' with | @mk Xg' tr' core' alg' alg_eq' R' => ?_
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hj := hs.jW
  clear hs
  change Xg' = t.r.z.Xg at hXg
  change tr' = t.r.z.tr at htr
  subst hXg htr
  change HEq core' _ at hcore
  have hc := eq_of_heq hcore
  subst hc
  have ha : alg' = GlobalTheory.Mem.R3.Tr.alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(Db.setDivZ Z N h).W, (Db.setDivZ Z N h).V, (Db.setDivZ Z N h).S, (Db.setDivZ Z N h).N, (Db.setDivZ Z N h).G⟩ t.r.z.alg := by
    apply Algebra.algebra_ext
    intro r
    apply (w.st (Db.setDivZ Z N h)).B.embLL.injective
    exact (by with_unfolding_all exact (((alg_eq' r).trans (t.r.z.alg_eq r).symm) :))
  subst ha
  change HEq R' _ at hR
  have hR2 := eq_of_heq hR
  subst hR2
  refine ⟨⟨?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((GeoCl.step (Γ := Γ) (D := (w.st Z).toD7) N h hp.geo) :))
  · exact (by with_unfolding_all exact ((lamAre_copy (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) N h (iK := t.r.z.alg) t.r.z.R t.r.z.F t.r.Z O.X
      (((divTr (D := w.D Z) N h O.X))) (((HEq.refl O.X.logLam))) (X0' := (p0')) (Y' := (Y')) ((Zr')) ((hj)) hp.lam) : _))

end GlobalTheory.Mem.OxMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem ell_eq_of_inRCone {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hlin : φ.LinearOn γ) (hsw : StrictWith bar φ N ℓ γ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring

end GlobalTheory.PolFan.StarKey
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace OrbMark

section Twist

variable {O : Type} [CommRing O]

def twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : Fin n → O := fun i => σ (a i)

@[simp] theorem twv_apply (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) (i : Fin n) : twv σ a i = σ (a i) := rfl

theorem twv_zero (σ : O ≃+* O) (n : ℕ) : twv σ (0 : Fin n → O) = 0 := funext fun _ => map_zero σ

theorem twv_smul (σ : O ≃+* O) {n : ℕ} (c : O) (a : Fin n → O) : twv σ (c • a) = σ c • twv σ a :=
  funext fun _ => by simp [twv]

theorem twv_twv (σ τ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv τ (twv σ a) = twv (σ.trans τ) a := rfl

theorem twv_symm_twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ.symm (twv σ a) = a :=
  funext fun _ => σ.symm_apply_apply _

theorem twv_twv_symm (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ (twv σ.symm a) = a :=
  funext fun _ => σ.apply_symm_apply _

def conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) : (Fin n → O) →ₗ[O] (Fin m → O) where
  toFun a := twv σ.symm (r (twv σ a))
  map_add' a b := by
    have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
    rw [e, map_add (f := _)]
    exact funext fun _ => map_add σ.symm _ _
  map_smul' c a := by
    rw [twv_smul, map_smul, twv_smul, RingHom.id_apply, σ.symm_apply_apply]

theorem twv_conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) (a : Fin n → O) :
    twv σ (conjLin σ r a) = r (twv σ a) := twv_twv_symm σ _

theorem conjLin_surjective (σ : O ≃+* O) {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) :
    Function.Surjective (conjLin σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (twv σ b)
  refine ⟨twv σ.symm a, ?_⟩
  show twv σ.symm (r (twv σ (twv σ.symm a))) = b
  rw [twv_twv_symm, ha, twv_symm_twv]

end Twist

section Mark

variable {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

def IsOrbForm (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Prop :=
  ∃ s : (Fin n → O) →ₗ[O] (X₀ ⧸ (CarDim.orad v : Submodule O X₀)), Function.Surjective s ∧
    ∀ (a b : Fin n → O) (x y : X₀), Submodule.Quotient.mk x = s a → Submodule.Quotient.mk y = s b →
      B (twv σ a) (twv σ b) = v x y

theorem isOrbForm_comp_iff (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) {n m : ℕ}
    {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) (B : (Fin m → O) → (Fin m → O) → ℝ) :
    IsOrbForm v σ n (fun a b => B (r a) (r b)) ↔ IsOrbForm v σ m B := by
  set r' := conjLin σ r
  have hr' : Function.Surjective r' := conjLin_surjective σ hr
  constructor
  · rintro ⟨s, hs, H⟩
    obtain ⟨t, ht⟩ := Module.projective_lifting_property r' LinearMap.id hr'
    have hrt : ∀ a, r' (t a) = a := fun a => LinearMap.congr_fun ht a
    have hker : ∀ z, r' z = 0 → s z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
      rw [← hx]
      refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
      obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
      have h1 := H (c • z) b (c • x) y (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
      have h2 := H 0 b 0 y (by rw [map_zero]; rfl) hb.symm
      have e : r (twv σ (c • z)) = 0 := by
        rw [← twv_conjLin, map_smul, hz, smul_zero, twv_zero]
      have e0 : r (twv σ 0) = 0 := by rw [twv_zero, map_zero]
      dsimp only at h1 h2
      rw [e] at h1
      rw [e0, map_zero, LinearMap.zero_apply] at h2
      exact_mod_cast h1.symm.trans h2
    refine ⟨s ∘ₗ t, fun y => ?_, fun a b x y hx hy => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      refine ⟨r' a, ?_⟩
      have : s (a - t (r' a)) = 0 := hker _ (by rw [map_sub, hrt, sub_self])
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    · have h := H (t a) (t b) x y hx hy
      dsimp only at h
      rwa [← twv_conjLin, ← twv_conjLin, hrt, hrt] at h
  · rintro ⟨s, hs, H⟩
    refine ⟨s ∘ₗ r', hs.comp hr', fun a b x y hx hy => ?_⟩
    have h := H (r' a) (r' b) x y hx hy
    show B (r (twv σ a)) (r (twv σ b)) = _
    rwa [twv_conjLin, twv_conjLin] at h

theorem eq_zero_of_isOrbForm_zero {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {B : (Fin 0 → O) → (Fin 0 → O) → ℝ}
    (h : IsOrbForm v σ 0 B) : v = 0 := by
  obtain ⟨s, hs, -⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  have hx : x ∈ (CarDim.orad v : Submodule O X₀) := by
    obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact (Submodule.Quotient.mk_eq_zero _).1 ha.symm
  simpa using hx 1 y

end Mark

section Fun

variable (O : Type) [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]


open Classical in
def orbFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) : InvFun O where
  toFun n B := if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0
  inv n m r hr B := by
    simp only [isOrbForm_comp_iff v _ hr]
  zero B := by
    rw [if_neg]
    rintro ⟨hv, σ, -, h⟩
    exact hv (eq_zero_of_isOrbForm_zero h)

variable {O}

open Classical in
theorem orbFun_toFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (orbFun O w0 v).toFun n B = if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0 := rfl

theorem orbFun_eval_eq_zero_or_one (w0 : O) (v : LinearMap.BilinForm ℤ X₀) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) : (orbFun O w0 v).eval X B = 0 ∨ (orbFun O w0 v).eval X B = 1 := by
  unfold InvFun.eval
  rw [orbFun_toFun]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_zero_of_isOrbForm_const {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {n : ℕ}
    (h : IsOrbForm v σ n fun _ _ => 0) : v = 0 := by
  obtain ⟨s, hs, H⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
  obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
  have := H a b x y ha.symm hb.symm
  simp only [LinearMap.zero_apply]
  have h0 : ((v x y : ℤ) : ℝ) = 0 := this.symm
  exact_mod_cast h0

theorem orbFun_evalZ_zero (w0 : O) {v : LinearMap.BilinForm ℤ X₀} (hv : v ≠ 0) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : (orbFun O w0 v).evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_neg]
  rintro ⟨-, σ, -, h⟩
  refine hv (eq_zero_of_isOrbForm_const (σ := σ) (n := n) ?_)
  simpa using h

theorem orbFun_evalZ_self (w0 : O) {v : LinearMap.BilinForm ℤ X₀} [Module.Finite O X₀] (hv : v ≠ 0)
    (hsym : ∀ y z, v y z = v z y) : (orbFun O w0 v).evalZ v = 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X₀
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_pos]
  refine ⟨hv, RingEquiv.refl O, rfl, (CarDim.orad v).mkQ ∘ₗ r, (Submodule.mkQ_surjective _).comp hr,
    fun a b x y hx hy => ?_⟩
  have hx' : x - r a ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hx
  have hy' : y - r b ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hy
  have e1 : v x y = v (r a) y := by
    have := hx' 1 y
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : v (r a) y = v (r a) (r b) := by
    have := hy' 1 (r a)
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero, hsym, hsym (r b)] at this
    exact this
  show ((v (r a) (r b) : ℤ) : ℝ) = (v x y : ℝ)
  rw [e1, e2]

end Fun

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]

theorem isTwInv_orbFun (H : Host E) (v : LinearMap.BilinForm ℤ X₀) : IsTwInv H (orbFun (𝓞 E) H.w0 v) := by
  intro τ hτ n B
  rw [orbFun_toFun, orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (twv τ (twv (σ.trans τ.symm) a)) (twv τ (twv (σ.trans τ.symm) b)) = _
    rw [twv_twv, twv_twv]
    convert this using 3 <;> ext i <;> simp

end Host

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPoint
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NearFrame

theorem dualMap_comp_near {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem exists_affine_frame_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), Tied e X j f₀ Eb A₀ → ∀ (y : CxPts X.str (σ.comp e.toRingHom)), ∀ A ∈ Eb.S (under y), ∃ (W : X.X.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(X.X, W)) (fW : EigFrame Z φ (((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι Z)), y ∈ ptsIn X.str (σ.comp e.toRingHom) W ∧ ∀ y' (hy' : y' ∈ ptsIn X.str (σ.comp e.toRingHom) W), (evHom hy').comp φ = σ ∧ ∃ g : EigFrame Z σ ((cxOf e σ hj y').1 ≫ genι Z), FrameAt e f₀ A₀ A y' g ∧ (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v fW embτ basisIdx) (evHom hy') g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ X j f₀ Eb A₀ hj hT y A hA
  obtain ⟨φz, fz, hx0, hφ0, hv0⟩ := hT.2 (under y) A hA
  have inj := IsFractionRing.injective (X.X.presheaf.stalk (under y)) X.X.functionField
  have hgen : spMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField) ≫ stalkPt X (under y) = genericPt X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have hstr : stalkPt X (under y) ≫ j ≫ genStr Z = spMap φz := by
    obtain ⟨p, hp⟩ := Spec.map_surjective (stalkPt X (under y) ≫ j ≫ genStr Z)
    have h1 : (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp p.hom =
        (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp φz := by
      refine EigLoc.spMap_inj ?_
      rw [← hφ0, ← TieBase.genericPt_str e X j hj, TieBase.spMap_trans, ← hgen]
      show _ ≫ Spec.map p = _
      rw [hp]
      simp only [Category.assoc]
    have h2 : p.hom = φz := RingHom.ext fun a => inj (RingHom.congr_fun h1 a)
    rw [← hp, ← h2]
    rfl
  obtain ⟨W, hW, φ, fW, hz, -, hWstr, hmap⟩ := _root_.GlobalTheory.ShFam.StalkSpread.exists_affine_isMap E H Dw l Xo c O β Z F X j (under y) φz fz ⊤ trivial hstr
  have hgerm : spMap (X.X.presheaf.germ W (under y) hz).hom ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) =
      stalkPt X (under y) := hW.fromSpecStalk_eq_fromSpecStalk hz
  have hφz : φz = (X.X.presheaf.germ W (under y) hz).hom.comp φ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hstr, ← hWstr, ← hgerm]
    simp only [Category.assoc]
  refine ⟨W, hW, φ, fW, mem_ptsIn.2 hz, fun y' hy' => ?_⟩
  have hz' : under y' ∈ W := mem_ptsIn.1 hy'
  have hp' : spMap (evHom hy') ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = y'.1 :=
    Points.specMap_valMap_fromSpec hW y'.1 hy'
  have ha : (evHom hy').comp φ = σ := by
    refine EigLoc.spMap_inj ?_
    rw [TieBase.spMap_trans, ← hWstr, ← (cxOf e σ hj y').2]
    show _ = (y'.1 ≫ j) ≫ genStr Z
    rw [← hp']
    simp only [Category.assoc]
  refine ⟨ha, ?_⟩
  obtain ⟨g, hg⟩ := EigFrame.exists_isMap fW (evHom hy') (φ' := σ) (x' := (cxOf e σ hj y').1 ≫ genι Z) ha.symm (by
    show (y'.1 ≫ j) ≫ genι Z = _
    rw [← hp']
    simp only [Category.assoc])
  refine ⟨g, ?_, hg⟩
  let germ' := (X.X.presheaf.germ W (under y') hz').hom
  let χ : X.X.presheaf.stalk (under y') →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) y'.1).hom
  have hχ : χ.comp germ' = evHom hy' := by
    show _ = (Points.valMap y'.1 W hy').hom
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.germ_stalkClosedPointTo]
    rfl
  have hgerm' : spMap germ' ≫ (show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) = stalkPt X (under y') :=
    hW.fromSpecStalk_eq_fromSpecStalk hz'
  obtain ⟨fz', hfz'⟩ := EigFrame.exists_isMap fW germ' (φ' := germ'.comp φ)
    (x' := stalkPt X (under y') ≫ j ≫ genι Z) rfl (by rw [← hgerm']; simp only [Category.assoc])
  have hκ : (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField).comp germ' =
      (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField).comp (X.X.presheaf.germ W (under y) hz).hom :=
    RingHom.ext fun a => (algebraMap_germ hz' a).trans (algebraMap_germ hz a).symm
  refine ⟨germ'.comp φ, fz', χ, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) y'.1).symm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hx0, ← hgerm, ← hgerm']
    simp only [← Category.assoc]
    rw [← TieBase.spMap_trans, ← TieBase.spMap_trans, hκ]
  · rw [hφ0, hφz, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hκ]
  · intro τ i
    have e : (fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y')) X.X.functionField)) ≫ fz'.v τ k) =
        fun k => spMap (dualMap (algebraMap (X.X.presheaf.stalk (under y)) X.X.functionField)) ≫ fz.v τ k := by
      funext k
      rw [hfz' τ k, hmap τ k, ← Category.assoc, ← Category.assoc, ← TieBase.spMap_trans, ← TieBase.spMap_trans,
        ← dualMap_comp_near, ← dualMap_comp_near, hκ]
    rw [e]
    exact hv0 τ i
  · intro τ i
    rw [hg τ i, hfz' τ i, ← Category.assoc, ← TieBase.spMap_trans, ← dualMap_comp_near, hχ]

end GlobalTheory.NearFrame
end
end

