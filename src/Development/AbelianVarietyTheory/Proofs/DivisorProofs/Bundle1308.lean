module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSquareSqMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pullback {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) :
    GlobalTheory.UPel.HT.OActN O ((Over.pullback f).obj A) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pullback_left {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) (c : O) :
    ((OActN.pullback f A a).act c).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (a.act c).left :=
  pullback.lift_fst _ _ _

end Act

section Sq

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

def sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : (G2 A').left ⟶ (G2 A).left :=
  (lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))).left

theorem pushPt_left (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (x : T ⟶ A') : (pushPt w x).left = x.left ≫ φ := rfl

theorem pushPt_comp (w : φ ≫ A.hom = A'.hom ≫ f) {T U : Over S'} (g : T ⟶ U) (x : U ⟶ A') :
    pushPt w (g ≫ x) = (Over.homMk g.left (by
      show g.left ≫ U.hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w g]) : Over.mk (T.hom ≫ f) ⟶ Over.mk (U.hom ≫ f)) ≫ pushPt w x :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem lift_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (a b : T ⟶ A') :
    (lift a b).left ≫ sqMap w = (lift (pushPt w a) (pushPt w b)).left := by
  have e := pushPt_comp w (lift a b) (fst A' A')
  have e' := pushPt_comp w (lift a b) (snd A' A')
  rw [lift_fst] at e
  rw [lift_snd] at e'
  rw [e, e', ← comp_lift]
  rfl

theorem isSquare_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : IsSquare φ (sqMap w) := by
  constructor
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ fst A A).left = _
    rw [lift_fst]; rfl
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ snd A A).left = _
    rw [lift_snd]; rfl

end Sq

section Tate

variable {p : ℕ} [Fact p.Prime]

def tateMoveO {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) : GlobalTheory.UPel.HT.TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem tateMoveO_ev {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (n : ℕ) (a : D.La) :
    (tateMoveO Φ hact he I).ev n a = Φ.symm (I.ev n a) := rfl

end Tate

section Pts

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem sqMap_of (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} {T₀ : Over S} (u : Over.mk (T.hom ≫ f) ⟶ T₀)
    (a' b' : T ⟶ A') (a b : T₀ ⟶ A) (ha : pushPt w a' = u ≫ a) (hb : pushPt w b' = u ≫ b) :
    (lift a' b').left ≫ sqMap w = u.left ≫ (lift a b).left := by
  rw [lift_sqMap, ha, hb, ← comp_lift]
  rfl

end Pts

end GlobalTheory.UPel.HT.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JB JA xᵀ yᵀ = GlobalTheory.WeilM.symp c ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Invertible (2 : R)]

def transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', d.form]
    rfl

variable {c}

theorem transD_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α β E) : (transD c d).e xᵀ = d.e x := by
  simp [transD]

theorem transD_rho {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (ψ : AddChar R ℂ) (w : Matrix β α E) :
    (transD c d).rho ψ w = d.rho ψ wᵀ := by
  simp [GlobalTheory.WeilM.Darboux.rho, transD]

variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ}
  {om : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem isUSplitting_inr (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inr _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inr _ _) (continuous_const.prodMk continuous_id)⟩
  have := h.impl (1, g) w φ hφ
  simpa [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB] using this

theorem isUSplitting_inl (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inl _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inl _ _) (continuous_id.prodMk continuous_const)⟩
  have := h.impl (g, 1) wᵀ φ hφ
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, transD_rho]
  convert this using 2
  simp [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, Matrix.transpose_mul]

end Gen

section Theta

variable (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)]

def thetaTr {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : W → ℂ :=
  fun w => GlobalTheory.WeilM.thetaSum F (d.rho ψ w Φ)

end Theta

section Transport

def IsTransport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {ξ : AE D}
    {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ))
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)) :
    Prop :=
  ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T),
    mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om (a, b) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
      thetaTr D.host.F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr D.host.F co ψ Φ)

end Transport

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaSignMultiplicative
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem ordL_mul [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {d : K} (hd : d ≠ 0) (x : K) : (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul (mul_ne_zero hσd hd) hx, ordL_mul hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem li_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    LinearIndependent K (fun i => (b i : Fin n → K)) :=
  b.linearIndependent.map' W.subtype W.ker_subtype

theorem span_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    Submodule.span K (Set.range fun i => (b i : Fin n → K)) = W := by
  have : (Set.range fun i => (b i : Fin n → K)) = W.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem gram_change (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = W) (hu' : LinearIndependent K u')
    (hsu' : Submodule.span K (Set.range u') = W) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det =
      σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det :=
  _root_.GlobalTheory.gram_det_change_of_bases σ W u u' hu hsu hu' hsu'

theorem csr_orth (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K) (hx : aeval γ Q *ᵥ x = 0) :
    ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 :=
  GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal σ γ hγ Q hQ x z hx

theorem gram_ne_zero (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A))
    (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0)
    (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 :=
  GlobalTheory.T.gram_det_ne_zero_of_ker_orth' σ A u hu hsu horth hdec

theorem conj_ker (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
      Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
      (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) =
        Matrix.of fun i j => ∑ k, σ (u i k) * u j k :=
  GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram σ γ g hg Q u hu hsu

end GlobalTheory.KapSignMul

namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem dec_of_dvd {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (Q : K[X]) (hsep : γ.charpoly.Separable)
    (hQ : Q ∣ γ.charpoly) : ∀ v, ∃ z y, aeval γ Q *ᵥ y = 0 ∧ v = aeval γ Q *ᵥ z + y := by
  obtain ⟨R, hR⟩ := hQ
  have hcop : IsCoprime Q R := Polynomial.Separable.isCoprime (by rw [← hR]; exact hsep)
  obtain ⟨a, c, hac⟩ := hcop
  intro v
  refine ⟨aeval γ a *ᵥ v, aeval γ (c * R) *ᵥ v, ?_, ?_⟩
  · rw [mulVec_mulVec, ← map_mul, show Q * (c * R) = c * (Q * R) by ring, ← hR, map_mul, aeval_self_charpoly,
      mul_zero, zero_mulVec]
  · rw [mulVec_mulVec, ← map_mul, ← add_mulVec, ← map_add (f := _), show Q * a + c * R = a * Q + c * R by ring, hac, map_one,
      one_mulVec]

theorem mem_im_of_coprime {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) {Q₁ Q₂ : K[X]} (hcop : IsCoprime Q₁ Q₂)
    {y : Fin n → K} (hy : aeval γ Q₂ *ᵥ y = 0) : ∃ z, y = aeval γ Q₁ *ᵥ z := by
  obtain ⟨a, c, hac⟩ := hcop
  refine ⟨aeval γ a *ᵥ y, ?_⟩
  have : y = aeval γ (a * Q₁ + c * Q₂) *ᵥ y := by rw [hac, map_one, one_mulVec]
  rw [mulVec_mulVec, ← map_mul, mul_comm Q₁ a]
  conv_lhs => rw [this]
  rw [map_add (f := _), add_mulVec, map_mul (aeval γ) c, ← mulVec_mulVec, hy, mulVec_zero, add_zero]

theorem ker_toLin' {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (P : K[X]) :
    LinearMap.ker (Matrix.toLin' (aeval M P)) = LinearMap.ker (aeval (Matrix.toLin' M) P) := by
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).toAlgHom M P).symm

theorem mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hs : ¬ IsSplitAt w) (γ : UL n w) :
    (((γ.1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (γ.1 : GLw n w) = 1 := by
  have := γ.2
  simp only [UL, if_neg hs] at this
  simpa [UJ, cT] using this

theorem mul_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : (M.map σ)ᵀ * M = 1) {Q₁ Q₂ : K[X]} (hsep : M.charpoly.Separable)
    (hdvd : Q₁ * Q₂ ∣ M.charpoly) (hcop : IsCoprime Q₁ Q₂) (hQ₁ : C (σ (Q₁.coeff 0)) * Q₁ = (Q₁.map σ).reverse)
    (hQ₂ : C (σ (Q₂.coeff 0)) * Q₂ = (Q₂.map σ).reverse) {ι₁ ι₂ ι : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι]
    (b₁ : Module.Basis ι₁ K (LinearMap.ker (Matrix.toLin' (aeval M Q₁))))
    (b₂ : Module.Basis ι₂ K (LinearMap.ker (Matrix.toLin' (aeval M Q₂))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k).det *
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k).det := by
  have hsup : LinearMap.ker (Matrix.toLin' (aeval M Q₁)) ⊔ LinearMap.ker (Matrix.toLin' (aeval M Q₂)) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    simp only [ker_toLin']
    exact sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop
  have hdis : Disjoint (LinearMap.ker (Matrix.toLin' (aeval M Q₁))) (LinearMap.ker (Matrix.toLin' (aeval M Q₂))) := by
    simp only [ker_toLin']
    exact disjoint_ker_aeval_of_isCoprime _ hcop
  have hli : LinearIndependent K (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K))) :=
    (li_coe b₁).sum_type (li_coe b₂) (by rw [span_coe, span_coe]; exact hdis)
  have hsp : Submodule.span K (Set.range (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)))) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_coe, span_coe, hsup]
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ (fun i => (b i : Fin n → K)) hli hsp (li_coe b) (span_coe b)
  have hblk : (Matrix.of fun i j => ∑ k, σ ((Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) i) k) *
      (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) j) k) =
      fromBlocks (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k)
        (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₂ j : Fin n → K) k) 0
        (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply, of_apply, Sum.elim_inr, Sum.elim_inl]
      have hy : aeval M Q₂ *ᵥ (b₂ i : Fin n → K) = 0 := by
        have := (b₂ i).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hx : aeval M Q₁ *ᵥ (b₁ j : Fin n → K) = 0 := by
        have := (b₁ j).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      obtain ⟨z, hz⟩ := mem_im_of_coprime M hcop hy
      rw [hz]
      exact csr_orth σ M hM Q₁ hQ₁ _ z hx
    · rfl
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  have h1 := gram_ne_zero σ (aeval M Q₁) _ (li_coe b₁) (span_coe b₁)
    (fun x z hx => csr_orth σ M hM Q₁ hQ₁ x z hx) (dec_of_dvd M Q₁ hsep (dvd_trans (dvd_mul_right _ _) hdvd))
  have h2 := gram_ne_zero σ (aeval M Q₂) _ (li_coe b₂) (span_coe b₂)
    (fun x z hx => csr_orth σ M hM Q₂ hQ₂ x z hx) (dec_of_dvd M Q₂ hsep (dvd_trans (dvd_mul_left _ _) hdvd))
  rw [hdet, sign_norm σ hσ hd, ordL_mul h1 h2, zpow_add₀ (by norm_num)]

theorem conj_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1) (Q : K[X])
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b' : Module.Basis ι' K (LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b' i : Fin n → K) k) * (b' j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det := by
  obtain ⟨hli, hsp, hgr⟩ := conj_ker σ γ g hg Q _ (li_coe b') (span_coe b')
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ _ (li_coe b) (span_coe b) hli hsp
  rw [hgr] at hdet
  rw [hdet, sign_norm σ hσ hd]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  intro E _ _ _ hU n _ w Q₁ Q₂ Q₃ γ g hsep hdvd hcop hc1 hc2
  by_cases hs : IsSplitAt w
  · simp [kapSign, hs]
  have hv := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hQ₁ : C (cj w (Q₁.coeff 0)) * Q₁ = (Q₁.map (cj w)).reverse := hc1.resolve_left hs
  have hQ₂ : C (cj w (Q₂.coeff 0)) * Q₂ = (Q₂.map (cj w)).reverse := hc2.resolve_left hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [kapSign, if_neg hs]
    exact mul_sign (cj w) hv _ (mem_UL hs γ) hsep hdvd hcop hQ₁ hQ₂ _ _ _
  · simp only [kapSign, if_neg hs]
    have hg' : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * γ * g := by simp
    rw [hg']
    exact conj_sign (cj w) hv γ.1 g.1 (mem_UL hs g) Q₃ _ _
  · simp only [kapSign, if_neg hs]
    rcases Int.even_or_odd (ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) i).1 k) * (Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) j).1 k).det) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow

end GlobalTheory.KapSignMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegralStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  first | exact @GlobalTheory.InertKatFrame.mem_KAt_of_frame | exact GlobalTheory.InertKatFrame.mem_KAt_of_frame | (intros; apply GlobalTheory.InertKatFrame.mem_KAt_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvAt0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colEq {d d₁ : ℕ} (h : d = d₁ + 2) : Fin d ≃ Fin d₁ ⊕ Fin 2 := (finCongr h).trans finSumFinEquiv.symm

def idx {n d d₁ : ℕ} (h : d = d₁ + 2) : Fin n × Fin d ≃ (Fin n × Fin d₁) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (colEq h)).trans (Equiv.prodSumDistrib _ _ _)


variable (σ : E →ₐ[F] E) {n d d₁ : ℕ} (h2 : Module.finrank F E = 2) (X : Spc F E n) (W : Spc F E d) {W₁ : Spc F E d₁}
  (h : d = d₁ + 2) (H' : Plane E d d₁) (M₁ : Model σ X W₁)

omit σ h2 X W H' M₁




end GlobalTheory.ThK.EvAt0
end
end

