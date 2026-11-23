module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
section
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cF (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

def latC (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))

def IsRat (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) : Prop :=
  matHom V γ = Formalism.UG.bc (incA D) γ'

def FinCong (V : HSp D) (N : ℕ) (k : GA D V) : Prop :=
  ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

structure IotaOK (Dw : Datum H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop where
  rt : (H.rt : D.host.E) = D.host.sqrtMinusD
  rt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD
  emb : LatEmb V ι
  isom : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

variable {Dw : Datum H} {l : Level H}

structure Ctx (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) : Type 1 where
  hr : V.rank = r
  g : ℕ
  e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  M : GlobalTheory.FrameUnif.ModelsOf F r
  ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)
  θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)
  x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

structure OK : Prop where
  iota : IotaOK Dw V C.ι
  pos : 1 ≤ Dw.p + Dw.q
  lA : l.A = 1
  good : GoodEmb c σ
  base : GlobalTheory.FrameUnif.ModelBase C.M
  modelW : ∀ k, ModelW V C.hr (C.M.X k)
  inf : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (C.θ τ)
  orth : ∀ k, IsOrthogonalFrame (C.M.X k) C.x₀

def th : ∀ k, (C.M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun _ τ => C.θ τ.1

def Mark (h : GA D V) (k : Fin C.F.n) (γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((C.M.X k).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((C.M.φ k (C.F.t k a) : Fin r → D.host.E) ∘ Fin.cast C.hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (C.ι a)) = (l.M : ℕ) • w

def fr (h : GA D V) (k : Fin C.F.n) : Frame (C.M.X k).Ψ r :=
  fun τ => (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) h) * C.x₀ τ.1 :
    Matrix (Fin r) (Fin r) ℂ)

def IsDict (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) : Prop :=
  (∀ h, ∃ γ, C.Mark h (dict h).1 γ ∧ (dict h).2 = C.fr (γ * h) (dict h).1) ∧
    ∀ k, ∃ h, dict h = ⟨k, C.fr 1 k⟩

def unf (un : ∀ k, (C.M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin C.F.n
  X := C.M.X
  un := un

end Ctx

structure PkgLaws {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (Kf : Subgroup (GA D V)) (χ : (AE D)ˣ →* Circle)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop where
  unf : IsUnf U
  unTest : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)
  chi1 : ∀ k la γ, (U.X k).χ la γ = 1
  modelW : ∀ k, ModelW V hr (U.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (U.X k) x₀
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  muVal : MuVal V χ mu
  adelAut : ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)
  expo : ∀ ρ, FJ.LatZ U.X ρ ∧ FJ.ExpoMatch U.X 1 ρ l.M
  dictLaws : ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr ∧
      DictLat U V hr dict ι e F ik φ th x₀

theorem cF_apply_eq_complexConj (D : D7) (x : D.host.E) : cF D x = IsCMField.complexConj D.host.E x := rfl

theorem mem_latC_iff_symm_mem (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨_, hv, V.frame.equivFun.apply_symm_apply v⟩

theorem coe_selfDualLatticeInFrameCoordinates_eq (V : HSp D) : (latC V : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  ext v
  rw [SetLike.mem_coe, mem_latC_iff_symm_mem, Module.Basis.equivFun_symm_apply]
  rfl

theorem exists_isRat_of_mem_GQ (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) : ∃ γ', IsRat V γ γ' := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ', e.symm⟩

theorem trace_model_eq_trace_hT (V : HSp D) {r : ℕ} (hr : V.rank = r) (u v : Fin V.rank → D.host.E) :
    Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (u ∘ Fin.cast hr.symm) (v ∘ Fin.cast hr.symm)) =
    -Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u)) := by
  subst hr
  have h : herm (GlobalTheory.RecDict.gmW V rfl) (u ∘ Fin.cast rfl) (v ∘ Fin.cast rfl) =
      -V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
      herm, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    show u a * (-V.gram b a) * cc (v b) = -(u a * (cc (v b) * V.gram b a))
    ring
  rw [h, neg_neg, mul_neg, map_neg]

theorem isom_iff_model (Dw : Datum H) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) :
    (∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))) ↔
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (ι x ∘ Fin.cast hr.symm) (ι y ∘ Fin.cast hr.symm)) := by
  have halt : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = -((Dw.EF y x : ℤ) : ℚ) := fun x y => by
    have h := Dw.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at h
    have h' : Dw.EF x y = -Dw.EF y x := by linarith
    rw [h', Int.cast_neg]
  simp only [trace_model_eq_trace_hT]
  constructor
  · intro h x y
    rw [halt, h]
  · intro h x y
    rw [halt, h, neg_neg]

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

end Ctx

end GlobalTheory.Member
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
section
noncomputable section
namespace GlobalTheory.RecDictModel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RecDict
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty}

theorem th_conj {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (z : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z) := by
  have hτ : ∀ x : D.host.E, τ (star x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hre : ∀ a : Ainf D.host.F, starRingEnd ℂ (θ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = θ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro a
    refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
      (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
    have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
      exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f |>.trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
    erw [e, h.1, ← hτ]
    rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  | tmul a x =>
    have e : ∀ y : D.host.E, a ⊗ₜ[D.host.F] y = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] (star x) := rfl
    rw [e2, e (star x), e x, map_mul, map_mul, map_mul, hre, h.1, h.1, hτ]

theorem cT_map {A : Type} [CommRing A] {n : Type} (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M : Matrix n n A) :
    (Formalism.UG.cT s M).map φ = (M.map φ).conjTranspose := by
  ext a b
  exact h _

theorem uni_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) (hM : Formalism.UG.cT s M * J * M = J)
    (J' M' : Matrix n n ℂ) (hJ : J.map φ = J') (hM' : M' = M.map φ) : M'.conjTranspose * J' * M' = J' := by
  subst hJ hM'
  rw [← cT_map s φ h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

set_option maxHeartbeats 800000 in
theorem archM_unitary (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) :
    (archM V θ g).conjTranspose * V.gram.map τ * archM V θ g = V.gram.map τ := by
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).1 * JR (AF D.host.F) V.gram * (matHom V g).1 =
      JR (AF D.host.F) V.gram := g.2
  let π : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hπ : ∀ z, π (sigR (AF D.host.F) D.sp.cm.sig z) = sigR (Ainf D.host.F) D.sp.cm.sig (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul a x => rfl
  have hJ : (JR (AF D.host.F) V.gram).map (θ.comp π) = V.gram.map τ := by
    ext a b
    exact h.1 _
  exact uni_map (sigR (AF D.host.F) D.sp.cm.sig) (θ.comp π) (fun z => (congrArg θ (hπ z)).trans (th_conj h (π z))) _ _ hg
    _ _ hJ rfl

theorem gram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = (x.conjTranspose * (G.map τ).transpose * x).transpose := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring



end GlobalTheory.RecDictModel
end
end

