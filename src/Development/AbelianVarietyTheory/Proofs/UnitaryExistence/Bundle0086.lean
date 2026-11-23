module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
section
noncomputable section

namespace GlobalTheory.HolEval

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section Ring

variable {K : Type} [Field K] {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {A : Type} [CommRing A] [Algebra K A]

theorem toC_mul (x y : CAt σ) : Formalism.L2.PjFree.toC (x * y) = Formalism.L2.PjFree.toC x * Formalism.L2.PjFree.toC y := rfl
theorem toC_add (x y : CAt σ) : Formalism.L2.PjFree.toC (x + y) = Formalism.L2.PjFree.toC x + Formalism.L2.PjFree.toC y := rfl
theorem toC_one : Formalism.L2.PjFree.toC (1 : CAt σ) = 1 := rfl

def holSub (B : Set V) (k : V → (A →ₐ[K] CAt σ)) : Subalgebra K A where
  carrier := {t | DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (k b t)) B}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_mul, toC_mul] at *
    exact hx.mul hy
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, map_add (f := _), toC_add] at *
    exact hx.add hy
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq, AlgHom.commutes]
    exact differentiableOn_const _

theorem mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {t : A} :
    t ∈ holSub B k ↔ DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (k b t)) B := Iff.rfl

theorem inv_mem_holSub {B : Set V} {k : V → (A →ₐ[K] CAt σ)} {d x : A} (hx : x ∈ holSub B k)
    (h : d * x = 1) : d ∈ holSub B k := by
  rw [mem_holSub] at hx ⊢
  have key : ∀ b, Formalism.L2.PjFree.toC (k b d) * Formalism.L2.PjFree.toC (k b x) = 1 := fun b => by
    rw [← toC_mul, ← map_mul, h, map_one, toC_one]
  have hne : ∀ b, Formalism.L2.PjFree.toC (k b x) ≠ 0 := fun b hb => by
    have h1 := key b
    rw [hb, mul_zero] at h1
    exact zero_ne_one h1
  have heq : (fun b => Formalism.L2.PjFree.toC (k b d)) = fun b => (Formalism.L2.PjFree.toC (k b x))⁻¹ :=
    funext fun b => eq_inv_of_mul_eq_one_left (key b)
  rw [heq]
  exact hx.inv fun b _ => hne b

theorem det_mem {n : ℕ} (A' : Subalgebra K A) (X : Matrix (Fin n) (Fin n) A) (h : ∀ i j, X i j ∈ A') :
    X.det ∈ A' := by
  rw [Matrix.det_apply]
  refine sum_mem fun e _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem evR_eq_of_frMap {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hS : Out.SecBaseChangeSt) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c w n)
    {S : Type} [CommRing S] [Algebra c.F S] (q : TRing c.F) (κ : q.R →ₐ[c.F] S) (u : FrPt Xo c q.R)
    (x : FrPt Xo c S) (h : FrMap κ u x) : evR Xo c f x = κ (f q u) := by
  have hW := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.1
  unfold sec secW at hf
  obtain ⟨hn, -⟩ := hf
  unfold evR evalAt
  split_ifs with hT
  · exact hW f hn S _ q _ κ _ u x hT.choose_spec.choose_spec.choose_spec h
  · exact absurd ⟨q, κ, u, h⟩ hT

end Ring

theorem differentiableOn_evR : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (evR Xo c f (y b))) B := by
  intro hS E _ _ _ H Dw l Xo c σ V _ _ B p y₀ ψ z y G a hzy hψ hG ha w n f hf
  obtain ⟨A, π, X, s, u, hU⟩ := _root_.GlobalTheory.Frames.exists_univFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨hFR, u₀, hπ, hch⟩ := hU
  have hk : ∀ b ∈ B, ∃ kk : A.R →ₐ[c.F] CAt σ,
      kk.comp π = ψ b ∧ (∀ τ, (X τ).map kk = G b τ) ∧ kk (s : A.R) = a b := by
    intro b hb
    obtain ⟨-, hc⟩ := hzy b hb
    obtain ⟨hex, huniq⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) (z b) (y b)
    obtain ⟨g, a', hdet, hc'⟩ := hex hc.1
    obtain ⟨hg, ha'⟩ := huniq _ _ _ _ hc hc'
    obtain ⟨kk, ⟨h1, h2, h3⟩, -⟩ := hFR.2 (CAt σ) (ψ b) g a' hdet
    exact ⟨kk, h1, fun τ => (h2 τ).trans (congrFun hg τ).symm, h3.trans ha'.symm⟩
  rcases B.eq_empty_or_nonempty with hB | ⟨b₀, hb₀⟩
  · rw [hB]
    exact differentiableOn_empty
  have : Nonempty (A.R →ₐ[c.F] CAt σ) := ⟨(hk b₀ hb₀).choose⟩
  choose! kk hkk using hk
  have hX : ∀ τ i j, X τ i j ∈ holSub B kk := by
    intro τ i j
    rw [mem_holSub]
    refine (hG τ i j).congr fun b hb => ?_
    show Formalism.L2.PjFree.toC (kk b (X τ i j)) = Formalism.L2.PjFree.toC (G b τ i j)
    rw [← (hkk b hb).2.1 τ]
    rfl
  have hs : (s : A.R) ∈ holSub B kk := by
    rw [mem_holSub]
    refine ha.congr fun b hb => ?_
    show Formalism.L2.PjFree.toC (kk b (s : A.R)) = Formalism.L2.PjFree.toC (a b)
    rw [(hkk b hb).2.2]
  have hA' := _root_.GlobalTheory.frameRing_subalgebra_eq_top c.F (E →+* ℂ) (fun τ => Dw.mult τ) p.R A.R π X s hFR (holSub B kk)
    (fun t => by
      rw [mem_holSub]
      refine (hψ t).congr fun b hb => ?_
      show Formalism.L2.PjFree.toC (kk b (π t)) = Formalism.L2.PjFree.toC (ψ b t)
      rw [← (hkk b hb).1]
      rfl)
    hX hs (inv_mem_holSub hs (Units.inv_mul s))
    (fun τ => by
      obtain ⟨v, hv⟩ := hFR.1 τ
      refine ⟨((v⁻¹ : (A.R)ˣ) : A.R), inv_mem_holSub (det_mem _ (X τ) (hX τ)) ?_, ?_⟩ <;>
        · rw [← hv]
          exact Units.inv_mul v)
  have he : f A u ∈ holSub B kk := by
    rw [hA']
    exact Algebra.mem_top
  rw [mem_holSub] at he
  refine he.congr fun b hb => ?_
  show Formalism.L2.PjFree.toC (evR Xo c f (y b)) = Formalism.L2.PjFree.toC (kk b (f A u))
  congr 1
  apply evR_eq_of_frMap hS hf A (kk b) u (y b)
  obtain ⟨hm, hc⟩ := hzy b hb
  have hb1 : FrMap (kk b) u₀ (z b) :=
    ((GlobalTheory.framedPoint_baseChange_laws E H Dw l Xo c).2.1 p.R A.R (CAt σ) π (kk b) y₀ u₀ (z b) hπ).2
      (by rw [(hkk b hb).1]; exact hm)
  apply (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A.R (CAt σ) (kk b) u₀ u (z b) (y b) X s hch hb1).2
  have e1 : (fun τ => (X τ).map (kk b)) = G b := funext (hkk b hb).2.1
  rw [e1, (hkk b hb).2.2]
  exact hc

end GlobalTheory.HolEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
section
noncomputable section

namespace GlobalTheory.FrameUnif

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem cover_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hT : CoverTri e F M) (y : FrPt Xo c (CAt σ)) :
    ∃ k, ∃ x : (M.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) y := by
  obtain ⟨k, x, Pm, hPm, hxy, hv⟩ := hT y
  obtain ⟨Pm', hPm', -, hx', hd', -⟩ := hun k x
  have hP : Pm' = Pm := by
    ext a j
    rw [hPm', hPm]
  subst hP
  refine ⟨k, x, ?_⟩
  have hxx : y.x = (un k x).x := hxy.symm.trans hx'.symm
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (un k x) y y).2.1 hxx fun τ i => ?_
  obtain ⟨cf, h1, h2, h3⟩ := hv (un k x).u hd' τ i
  exact ⟨cf, h1, h2, by rw [← hxx]; exact h3⟩

theorem fibre_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un)
    (hM : ModelBase M) (hB : FibTri e F M) (k k' : Fin F.n) (x : (M.X k).dom) (x' : (M.X k').dom) :
    (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k' x')) ↔
      ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r,
        (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩ := by
  constructor
  · rintro ⟨t, hx, hu, -⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun.1 k x
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun.1 k' x'
    refine hB k k' x x' Pm Pm' (un k x).u (un k' x').u hPm hPm' (hxP.symm.trans (hx.symm.trans hxP')) hd hd'
      fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    rw [hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, heq⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
    have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
    have hxg : lact γ x.1 ∈ (M.X k').dom := (hM.domStab k' x.1 x.2).2 γ hγ
    obtain ⟨t1, ht1, -⟩ := hun.2.2.1 k' γ hγ x hxg
    have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
      have hx2 := x'.2
      rw [h3] at hx2
      exact hx2
    obtain ⟨t2, ht2, -⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
    have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
    rw [hx'] at ht2
    exact ⟨t2 * t1, (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ _).2.2.1 t1 t2 ht1 ht2⟩

theorem rdU_of_mem (U : Formalism.L2.PjFree.Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r}
    (h : x ∈ (U.X k).dom) : Formalism.L2.PjFree.rdU U f k x = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [Formalism.L2.PjFree.rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos h]

theorem readSec_unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un) (hM : ModelBase M)
    (hW : ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → (CAt σ)ˣ)
      (y y' : FrPt Xo c (CAt σ)), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y) :
    ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k,
      ((unfOf e F M un).X k).IsSec (laU (unfOf e F M un) a n k) (Formalism.L2.PjFree.rdU (unfOf e F M un) f k) := by
  intro a n hd f hf k
  refine ⟨hun.2.2.2 a n hd f hf k, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hxb : rmul x b ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).1 b hb
    obtain ⟨t, ht, hw⟩ := hun.2.1 k ⟨x, hx⟩ b hb hxb
    refine (rdU_of_mem _ f k hxb).trans ?_
    rw [rdU_of_mem _ f k hx, ← hw a n hd]
    exact congrArg Formalism.L2.PjFree.toC (hW a n f hf t _ _ ht)
  · have hxg : lact γ x ∈ ((unfOf e F M un).X k).dom := (hM.domStab k x hx).2 γ hγ
    obtain ⟨t, ht, hw⟩ := hun.2.2.1 k γ hγ ⟨x, hx⟩ hxg
    refine (rdU_of_mem _ f k hxg).trans ?_
    rw [rdU_of_mem _ f k hx, show ((unfOf e F M un).X k).χ (laU (unfOf e F M un) a n k) γ = 1 from hM.chi k _ γ,
      ← hw a n hd]
    exact congrArg Formalism.L2.PjFree.toC (hW a n f hf t _ _ ht)

end

theorem isUnf_built : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → FramesOK e F M un → IsUnf (unfOf e F M un) := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un hσ hM hN hun
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  exact ⟨hM.rank, hM.type,
    cover_unfOf e F M un hun.1 (GlobalTheory.CoverFrame.coverTri E H Dw l Xo c σ g e F r M hσ hM hN),
    fibre_unfOf e F M un hun hM (GlobalTheory.FibreFlag.fibTri E H Dw l Xo c σ g e F r M hσ hM hN),
    readSec_unfOf e F M un hun hM ((GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred),
    g, e, F, id, M.φ, hM.ef, hun.1⟩

end GlobalTheory.FrameUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
section
section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevStab

open GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_isometry_of_hol {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (ha : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hhol : IsHolTo Set.univ (fun z => (e z).left)) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 ha hs hhol
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem map_mem_smul_top {R L L' : Type*} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (I : Ideal R) (f : L →ₗ[R] L') {x : L} (hx : x ∈ I • (⊤ : Submodule R L)) : f x ∈ I • (⊤ : Submodule R L') := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_levAut (F : FamilyUnif Xo σ ty) {s : Sim D} {ρ : Xo.X ≅ Xo.X} (hρ : Xo.LevAut s ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ.hom = F.u j P') :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La, (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      ∀ a, gam (F.t i (s.f l.M a)) - F.t j a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
  obtain ⟨-, ν, hη, -⟩ := hρ
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ.hom ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  refine ⟨gam, hEF, fun a => ?_⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  have hxm : gam (F.t i (s.f l.M x)) - F.t j x ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) :=
    Submodule.sub_mem _ (map_mem_smul_top _ gam.toLinearMap (map_mem_smul_top _ _ (map_mem_smul_top _ _ hx₀)))
      (map_mem_smul_top _ _ hx₀)
  have hym : gam (F.t i (s.f l.M y)) - F.t j y ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di j).La) := by
    obtain ⟨v, hv⟩ : ∃ v, gam (F.t i (s.f l.M y)) = F.t j y + l.M • v := by
      refine (div_eq_iff hP'.2.1 (F.ex_add j P' hP') (F.ex_ker j P' hP') hM0 _ _).1 ?_
      rw [hh, ← map_smul h, hx, ← F.ex_eta j P' hP' y hy, ← F.ex_eta i P hP _ (map_mem_smul_top _ _ hy)]
      apply Over.OverMorphism.ext
      rw [hβ]
      change (F.u i P ≫ (Xo.univ.eta (s.f l.M y)).left) ≫ ν.φ = F.u j P' ≫ (Xo.univ.eta y).left
      rw [Category.assoc, hη, ← Category.assoc, hu]
    rw [hv, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine Submodule.smul_mem_smul ?_ trivial
    have hM : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) hM
  have := Submodule.add_mem _ hxm hym
  rwa [sub_add_sub_comm, ← map_add, ← map_add, ← map_add, ← map_add] at this

end GlobalTheory.LevStab

end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem test_value_eq_const_mul_reading : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), IsUnf U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ sec Xo c a n, Formalism.L2.PjFree.toC (ψ (f p y)) = u * Formalism.L2.PjFree.rdU U f k x.1 := by
  intro hSB E _ _ _ H Dw l Xo c σ r U hU a n p y ψ
  obtain ⟨-, -, hWD, -, -, -, hBor⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hSB E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hSB E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨-, -, hcov, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := hcov z
  have hred : _root_.IsReduced (CAt σ) := by
    unfold CAt
    exact isReduced_of_noZeroDivisors
  refine ⟨k, x, Formalism.L2.PjFree.toC (wchar (ex Dw a n) t), ?_⟩
  intro f hf
  have hf' := hf
  unfold sec secW at hf'
  obtain ⟨hN, -⟩ := hf'
  have h1 : evR Xo c f z = ψ (f p y) := by
    have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
    unfold evR evalAt
    rw [dif_pos hT]
    exact hWD f hN _ _ _ _ _ _ _ _ hT.choose_spec.choose_spec.choose_spec hz
  have h2 : Formalism.L2.PjFree.rdU U f k x.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) := by
    unfold Formalism.L2.PjFree.rdU
    exact dif_pos x.2
  have h3 := hBor (CAt σ) hred a n f hf t (U.un k x) z ht
  rw [← h1, h2, h3]
  rfl

end GlobalTheory.FrameUnif
end

