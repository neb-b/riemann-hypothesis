module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FinAtQ

section Abs

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] [Algebra S R]

def mulSub (L : Submodule S (n → R)) (g : ℕ) : AddSubgroup L where
  carrier := {y | ∃ z : L, (y : n → R) = g • (z : n → R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by simp [hz, hw, smul_add]⟩
  neg_mem' := by
    rintro a ⟨z, hz⟩
    exact ⟨-z, by simp [hz]⟩

def actL (L : Submodule S (n → R)) (x : GL n R) (hx : x ∈ stabGL L) : L →+ L where
  toFun y := ⟨(x : Matrix n n R) *ᵥ (y : n → R), (hx y).1 y.2⟩
  map_zero' := by ext1; simp
  map_add' a b := by ext1; simp [Matrix.mulVec_add]

theorem mulSub_le_comap (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    mulSub L g ≤ (mulSub L g).comap (actL L x hx) := by
  rintro y ⟨z, hz⟩
  refine ⟨actL L x hx z, ?_⟩
  simp only [actL, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hz, Matrix.mulVec_smul]

def actQ (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    (L ⧸ mulSub L g) →+ (L ⧸ mulSub L g) :=
  QuotientAddGroup.map _ _ (actL L x hx) (mulSub_le_comap L g x hx)

theorem actQ_mk (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) (y : L) :
    actQ L g x hx (y : L ⧸ mulSub L g) = ((actL L x hx y : L) : L ⧸ mulSub L g) := rfl

def rho (L : Submodule S (n → R)) (g : ℕ) (W : Subgroup (GL n R)) (hW : W ≤ stabGL L) :
    W →* AddMonoid.End (L ⧸ mulSub L g) where
  toFun x := actQ L g x (hW x.2)
  map_one' := by
    show actQ L g 1 _ = AddMonoidHom.id _
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [actQ_mk]
      congr 1
      ext1
      simp [actL]
  map_mul' a b := by
    show actQ L g (a * b : W) _ = (actQ L g a (hW a.2)).comp (actQ L g b (hW b.2))
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [AddMonoidHom.comp_apply, actQ_mk, actQ_mk, actQ_mk]
      congr 1
      ext1
      simp [actL, Matrix.mulVec_mulVec]

theorem finiteIndex_of_trivOn (L : Submodule S (n → R)) (g : ℕ) (hQ : Finite (L ⧸ mulSub L g))
    (H W : Subgroup (GL n R)) (hW : W ≤ stabGL L)
    (hH : ∀ x ∈ W, (∀ y ∈ L, ∃ z ∈ L, (x : Matrix n n R) *ᵥ y - y = g • z) → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  have hE : Finite (AddMonoid.End (L ⧸ mulSub L g)) :=
    Finite.of_injective (fun f : AddMonoid.End (L ⧸ mulSub L g) => (f : (L ⧸ mulSub L g) → (L ⧸ mulSub L g)))
      (fun a b h => AddMonoidHom.ext (congrFun h))
  have hU : Finite (AddMonoid.End (L ⧸ mulSub L g))ˣ := Finite.of_injective _ Units.val_injective
  have h1 : (rho L g W hW).toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := (rho L g W hW).toHomUnits.ker) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : rho L g W hW x = 1 := congrArg Units.val hx
  rw [Subgroup.mem_subgroupOf]
  refine hH x x.2 fun y hy => ?_
  have h2 : actQ L g x (hW x.2) ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) = ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) :=
    DFunLike.congr_fun hx' _
  rw [actQ_mk, QuotientAddGroup.eq] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨-(z : n → R), (-z).2, ?_⟩
  have hz' : -(((x : GL n R) : Matrix n n R) *ᵥ y) + y = g • (z : n → R) := by
    simpa [actL] using hz
  rw [smul_neg, ← hz', neg_add, neg_neg, sub_eq_add_neg, add_comm]

end Abs

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_quot (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (g : ℕ) (hg : g ≠ 0) :
    Finite (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ ⧸
      mulSub (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) g) := by
  set L := latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ with hL
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  let m : Fin k → Fin n → E := fun i => (s i : Fin n → E)
  have hm : ∀ i, m i ∈ Λ := fun i => (s i).2
  have hgen : ∀ l ∈ Λ, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i := by
    intro l hl
    have h0 : (⟨l, hl⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h0
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at h1
    simpa [m] using h1.symm
  have key := fun y => PI.LPI.plGen F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Λ m hm hgen y
  let c : v.adicCompletionIntegers F := (g : v.adicCompletionIntegers F)
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    simp [c, hg] at h1
  haveI : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let sec : v.adicCompletionIntegers F ⧸ Ideal.span {c} → v.adicCompletionIntegers F :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hmemf : ∀ a : Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c},
      (fun j => ∑ i, m i j ⊗ₜ[F] ((sec (a i) : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ L :=
    fun a => (key _).2 ⟨fun i => (sec (a i) : v.adicCompletion F), fun i => (sec (a i)).2, rfl⟩
  let f : (Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c}) → L ⧸ mulSub L g :=
    fun a => ((⟨_, hmemf a⟩ : L) : L ⧸ mulSub L g)
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨a, ha, hy⟩ := (key y).1 y.2
  refine ⟨fun i => Ideal.Quotient.mk _ ⟨a i, ha i⟩, ?_⟩
  have hd : ∀ i, ∃ b : v.adicCompletionIntegers F,
      (sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) = ⟨a i, ha i⟩ + b * c := by
    intro i
    have h := Function.surjInv_eq (f := Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _ ⟨a i, ha i⟩)
    rw [Ideal.Quotient.eq] at h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    exact ⟨b, by rw [hb]; ring⟩
  choose b hb using hd
  show ((⟨_, hmemf _⟩ : L) : L ⧸ mulSub L g) = (y : L ⧸ mulSub L g)
  rw [QuotientAddGroup.eq]
  refine ⟨⟨fun j => ∑ i, m i j ⊗ₜ[F] (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F),
    (key _).2 ⟨_, fun i => (-(b i)).2, rfl⟩⟩, ?_⟩
  funext j
  have e1 : ∀ i, ((sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      a i + g • (b i : v.adicCompletion F) := by
    intro i
    rw [hb i]
    simp [c, nsmul_eq_mul, mul_comm]
  have hneg : ∀ i, (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      -((b i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun i => rfl
  rw [Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hy]
  simp only [e1, hneg, TensorProduct.tmul_add, Finset.sum_add_distrib, TensorProduct.tmul_smul,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_neg]
  abel

end Fin

section Gen

open Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finiteIndex_of_princ (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (hΛ : Module.Finite (𝓞 E) Λ) (N : ℕ) (hN : 0 < N)
    (H W : Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hW : W ≤ levelVL hc.sig S.gram v Λ) (hH : ∀ x, InPrinc hc S v N Λ x → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  refine finiteIndex_of_trivOn _ N (finite_quot v Λ hΛ N hN.ne') H W (hW.trans inf_le_right) ?_
  intro x hx htriv
  apply hH
  refine ⟨hW hx, ?_⟩
  intro y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  exact ⟨z, hz, by rw [e, Nat.cast_smul_eq_nsmul]⟩

end Gen


set_option maxHeartbeats 1600000 in
theorem chartLoc_finiteIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hle := GlobalTheory.T.chart_localGroup_le_baseLattice_level I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb
  obtain ⟨N, hN, hpr⟩ :=
    GlobalTheory.T.chart_local_group_contains_principal_congruence I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hfin : Module.Finite (𝓞 (I.rec7 l Z).host.E) Lb0 := by
    have h0 := (F u).levJ.Lb_fin
    rw [hLb] at h0
    unfold reL at h0
    refine (Module.Finite.equiv_iff (Submodule.equivMapOfInjective
      ((reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).toLinearMap.restrictScalars
        (𝓞 (I.rec7 l Z).host.E))
      (reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).injective Lb0)).mpr ?_
    exact h0
  exact finiteIndex_of_princ _ _ v Lb0 hfin N hN _ _ (iSup_le fun β' => hle β' v hv) hpr

end GlobalTheory.Mem.Col2.FinAtQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopPartHodgeMetricUniformisationImage
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifDens


open Filter Topology GlobalTheory.UnifDens in
theorem chernTopPart_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ A hAD hAm hinj
  have hdim := _root_.GlobalTheory.BaseDim.card_eq_dim E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hcont, hana⟩ := _root_.GlobalTheory.UnifHolo.unif_continuousOn_analyticAt E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have h3a := _root_.GlobalTheory.UnifDens.chernTop_unif_chart E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  have h3b := _root_.GlobalTheory.UnifDens.chernTop_domain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  set D := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hDdef
  have hDo : IsOpen D := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set L := flatL hdim with hLdef
  set C : ℝ := grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef, grassConst]
    refine pow_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity)) _
  set dens : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → ℝ := fun w =>
    ∏ i, ((hQ (unflat w i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) with hdens
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set ρ : AlgChart X.str (σ.comp e.toRingHom) X.dim → CxPts X.str (σ.comp e.toRingHom) → ENNReal := fun ch y =>
    ENNReal.ofReal ((((1 : ℤˣ) : ℤ) : ℝ) * chernTop (pointPoly H Dw)
      (fun v => lieGram e U hj f₀ A₀ (Eb.nonempty (under y)).choose (ch.e.symm v)) (ch.e y)) with hρ
  have hμ : chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 =
      glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ := rfl
  have hpre : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (D ∩ ψ ⁻¹' S) := by
    intro S hS
    have hm : Measurable (D.restrict ψ) := (continuousOn_iff_continuous_restrict.1 hcont).measurable
    have := hDo.measurableSet.subtype_image (hm hS)
    convert this using 1
    ext w
    constructor
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hw⟩, hwS, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwS, rfl⟩
      exact ⟨hw, hwS⟩
  have key : ∀ (ch : AlgChart X.str (σ.comp e.toRingHom) X.dim)
      (B : Set ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ)), MeasurableSet B → B ⊆ D → Set.InjOn ψ B →
      chartMeas ch.e (ρ ch) (ψ '' B) = ENNReal.ofReal C * μD (B ∩ ψ ⁻¹' ch.e.source) := by
    intro ch B hB hBD hBi
    set B' := B ∩ ψ ⁻¹' ch.e.source with hB'
    have hB'm : MeasurableSet B' := by
      have e0 : B' = B ∩ (D ∩ ψ ⁻¹' ch.e.source) := by
        ext w
        simp only [hB', Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, hBD h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      rw [e0]
      exact hB.inter (hcont.isOpen_inter_preimage hDo ch.e.open_source).measurableSet
    have hψB : MeasurableSet (ψ '' B) := hB.image_of_continuousOn_injOn (hcont.mono hBD) hBi
    rw [chartMeas_apply ch.e (ρ ch) hψB]
    have e1 : ch.e.source ∩ ψ '' B = ψ '' B' := by
      rw [hB', Set.image_inter_preimage, Set.inter_comm]
    set φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (L u)) with hφ
    set S := L ⁻¹' B' with hS
    have e2 : ch.e '' (ψ '' B') = φ '' S := by
      rw [hS, hφ, ← Set.image_image (fun w => ch.e (ψ w)) L, Set.image_preimage_eq _ L.surjective,
        Set.image_image]
    have hSm : MeasurableSet S := L.continuous.measurable hB'm
    have hdiff : ∀ u ∈ S, DifferentiableAt ℂ φ u := by
      intro u hu
      have hu' : L u ∈ B' := hu
      exact (hana (L u) (hBD hu'.1) ch hu'.2).differentiableAt.comp u L.differentiableAt
    have hder : ∀ u ∈ S, HasFDerivWithinAt φ ((fderiv ℂ φ u).restrictScalars ℝ) S u :=
      fun u hu => ((hdiff u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjφ : Set.InjOn φ S := by
      intro u1 h1 u2 h2 h12
      have h1' : L u1 ∈ B' := h1
      have h2' : L u2 ∈ B' := h2
      have h3 : ψ (L u1) = ψ (L u2) := ch.e.injOn h1'.2 h2'.2 h12
      exact L.injective (hBi h1'.1 h2'.1 h3)
    rw [e1, e2, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinjφ]
    have hint : ∀ u ∈ S, ENNReal.ofReal |((fderiv ℂ φ u).restrictScalars ℝ).det| * ρ ch (ch.e.symm (φ u)) =
        ENNReal.ofReal (C * dens (L u)) := by
      intro u hu
      have hu' : L u ∈ B' := hu
      have hsym : ch.e.symm (φ u) = ψ (L u) := ch.e.left_inv hu'.2
      rw [hsym]
      have hdet : ((fderiv ℂ φ u).restrictScalars ℝ).det =
          Complex.normSq (LinearMap.det (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) := by
        have := LinearMap.det_restrictScalars (R := ℝ)
          (f := (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim))
        rw [Algebra.norm_complex_apply] at this
        exact this
      have hA := (Eb.nonempty (under (ψ (L u)))).choose_spec
      have ha := h3a u (hBD hu'.1) ch hu'.2 _ hA
      have hb := h3b u (hBD hu'.1) _ hA
      rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _), hρ, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
      congr 1
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [← ha, hb]
    rw [setLIntegral_congr_fun hSm hint]
    have hmp := (flatL_mp hdim).setLIntegral_comp_preimage_emb L.toHomeomorph.measurableEmbedding
      (fun w => ENNReal.ofReal (C * dens w)) B'
    rw [hS]
    refine hmp.trans ?_
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hμD, muD, withDensity_apply _ hB'm,
      Measure.restrict_restrict hB'm, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBD)]

  set ν : Measure (CxPts X.str (σ.comp e.toRingHom)) := ENNReal.ofReal C • Measure.map ψ (μD.restrict A) with hν
  have hae : AEMeasurable ψ (μD.restrict A) := (hcont.mono hAD).aemeasurable hAm
  have hνT : ∀ S, MeasurableSet S → ν S = ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.smul_apply, Measure.map_apply_of_aemeasurable hae hS, Measure.restrict_apply' hAm,
      Set.inter_comm, smul_eq_mul]
  have hAS : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (A ∩ ψ ⁻¹' S) := by
    intro S hS
    have e0 : A ∩ ψ ⁻¹' S = A ∩ (D ∩ ψ ⁻¹' S) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨h.1, hAD h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e0]
    exact hAm.inter (hpre S hS)
  have hψA : MeasurableSet (ψ '' A) := hAm.image_of_continuousOn_injOn (hcont.mono hAD) hinj
  have hle : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) ≤ ν := by
    rw [glueMeas, GlobalTheory.ChernScale.restrict_iSup_eq _ hψA]
    refine iSup_le fun ch => Measure.le_iff.2 fun S hS => ?_
    rw [Measure.restrict_apply hS, hνT S hS, Set.inter_comm, ← Set.image_inter_preimage,
      key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left)]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have heq : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) = ν := by
    refine ext_of_cover (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e.source)
      (fun ch => ch.e.open_source) (fun y => AlgChart.exists_mem_source y) fun ch S hS hSc =>
        le_antisymm (Measure.le_iff'.1 hle S) ?_
    rw [Measure.restrict_apply hS, hνT S hS]
    have e3 : A ∩ ψ ⁻¹' S = (A ∩ ψ ⁻¹' S) ∩ ψ ⁻¹' ch.e.source :=
      (Set.inter_eq_left.2 fun w (hw : w ∈ A ∩ ψ ⁻¹' S) => hSc hw.2).symm
    calc ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S)
        = chartMeas ch.e (ρ ch) (ψ '' (A ∩ ψ ⁻¹' S)) := by
          rw [key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left), ← e3]
      _ = chartMeas ch.e (ρ ch) (S ∩ ψ '' A) := by rw [Set.image_inter_preimage, Set.inter_comm]
      _ ≤ glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ (S ∩ ψ '' A) :=
          Measure.le_iff'.1 (le_iSup (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => chartMeas ch.e (ρ ch)) ch) _
  rw [hμ, ← Measure.restrict_apply_self, heq, hνT _ hψA, Set.inter_eq_left.2 (Set.subset_preimage_image ψ A)]

end GlobalTheory.UnifDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSimplicialLabelledFanRefinement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_simpLab_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ φ lab : InvFun (𝓞 E), IsPolyFan H.bar q φ ∧ IsTwInv H φ ∧ IsTwInv H lab ∧ SimpLab H.bar q φ lab ∧ Subordinate H.bar q φ ψ := by
  intro E _ _ _ H q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := _root_.GlobalTheory.PolFan.CarDim.exists_isCarrierDim E H q ψ hD hψ hT
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.PolFan.carrierDim_bounded E H q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun (𝓞 E), IsTwInv H φ ∧ IsBaryStage H.bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact _root_.GlobalTheory.PolFan.baryStep E H q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ H.bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodChartHodgeMetricGenericFibre
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.PerChart

theorem exists_periodChart_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, d, hP, hE, hx₀, h0, hcard, hd, hInner, hR⟩ :=
    _root_.GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart E H Dw l Xo c O β Y T σ U hσ hU x₀
  obtain ⟨κ, hκ, hM⟩ := _root_.GlobalTheory.HodgeChart.hodgeMet_eq_riem_chart E H Dw l Xo c O β Y T σ U hσ hU n a ha g ch₀ ex hE hcard hInner
  refine ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, fun τ => κ τ * d, hP, hE, hx₀, h0, hcard,
    fun τ => mul_pos (hκ τ) hd, hInner, ?_⟩
  intro x hx hin f W hW
  obtain ⟨h1, h2⟩ := hM x hx hin _ (hR x hx hin) f W hW
  have hs : ∀ (M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ),
      hermForm (((d : ℝ) : ℂ) • M) v w = ((d : ℝ) : ℂ) * hermForm M v w := by
    intro M v w
    simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · rw [h1 τ]
    ext b b'
    simp only [Matrix.smul_apply, Matrix.of_apply, hs, smul_eq_mul]
    push_cast
    ring
  · have := h2 p q hpq
    rw [hs] at this
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd.ne')

end GlobalTheory.ShFam.Hor.PerChart
end

