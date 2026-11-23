module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev intR : Type := integralClosure ℤ_[l] Lf

def intEmb : intR Lf →+* PadicAlgCl l := Lf.val.toRingHom.comp (algebraMap (integralClosure ℤ_[l] Lf) Lf)

end Ring

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

def EvOk (i : E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) : Prop :=
  (∀ x, ev (1 ⊗ₜ[F] x) = i x) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev (a ⊗ₜ[F] 1)‖ ≤ 1) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[F] 1) = 0) ∧
    ∀ y, ev y ∈ IntermediateField.adjoin ℚ_[l] (Set.range i)

end Adeles

def incOf (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) :
    D.host.E →+* PadicAlgCl l :=
  cond b (cj (e0.comp (labLL D τ))) (e0.comp (labLL D τ))

def HalfAt (D : D7) (l : ℕ) : Prop := ∀ [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool), IsHalf (incOf D e0 b)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def Ix (j : Fin D.R.m) (t : p.P.T) (l N : ℕ) : Type :=
  {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal}

def frameOf (j : Fin D.R.m) (t : p.P.T) (l : ℕ) [Fact l.Prime] (N : ℕ) (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] Lf] (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ) :
    Frame l D.what₂.Tau N where
  O := intR Lf
  emb := intEmb Lf
  G := Bridge.Gf (Vc D j)
  Γ := (Bridge.ratF (Vc D j)).range
  K := levJ p j t
  kap := kap
  chi := chi
  I := Ix p j t l N
  tr i := hkA p j t i.1
  cst _ := 1

def kapMat (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ : levJ p j t) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) (PadicAlgCl l) :=
  ((bs τ)⁻¹).val * ((matOf j (κ : Bridge.Gf (Vc D j))).map (ev τ)).submatrix rk rk * (bs τ).val

def KapEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) : Prop :=
  ∀ κ τ, (Matrix.GeneralLinearGroup.map (intEmb Lf) (kap κ τ)).val = kapMat p j t ev bs rk κ τ

def ChiEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (io : PadicAlgCl l ≃+* ℂ) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)} (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf)))
    (chi : levJ p j t →* (intR Lf)ˣ) : Prop :=
  ∀ κ, io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1

def KapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (rk : Fin P.Nr ≃o Fin (Vc D j).rank), (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) →
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) →
    ∃ bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, bs τ = 1) ∧ ∀ κ τ a c,
      kapMat p j (p.R.mu w) ev bs rk κ τ a c ∈ IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ∧
        ‖kapMat p j (p.R.mu w) ev bs rk κ τ a c‖ ≤ 1

def ChiAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ κ : levJ p j (p.R.mu w), ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ) ^ M = 1

def ClassesAt (j : Fin D.R.m) (t : p.P.T) : Prop :=
  ∃ S : Finset (Bridge.Gf (Vc D j)), ∀ g, ∃ γ ∈ (Bridge.ratF (Vc D j)).range, ∃ s ∈ S, ∃ κ ∈ levJ p j t, g = γ * s * κ

def TameAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ g : Bridge.Gf (Vc D j),
    Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} ∧
      ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ Nat.card {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)}

def ChoiceOk (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))}
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ) : Prop :=
  (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) ∧ (∀ x, e0 x ∈ Lf) ∧ (∀ x, io (e0 x) = D.what₂.embLL x) ∧
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) ∧ KapEq p j (p.R.mu w) ev bs rk kap ∧ ChiEq p j (p.R.mu w) io sh kap chi


open Classical in
def PermAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
      (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ


open Classical in
def CommAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i i', ∃ σ : F.tr i × F.tr i' ≃ F.tr i' × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

def ReadsAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (b : Bool) (sh : D.what₂.Tau → ℤ),
    ∀ (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi → (∀ τ, bs τ = 1) →
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi) W.lam (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val

end Point

end GlobalTheory.FrameOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem hasOp_one (ψ : AddChar (AF F) ℂ) : HasOp (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl⟩

theorem hasOp_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOp ψ G) (hG' : HasOp ψ G') :
    HasOp ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul]
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul]
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]

theorem hasOp_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOp ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOp ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOp_one ψ) (fun _ _ _ _ hx hy => hasOp_mul hx hy) hG

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl (F := F)) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl (F := F)) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange

open GlobalTheory.SympChange in
theorem GlobalTheory.SympChange.change_of_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOp B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact GlobalTheory.T.weil_operator_for_levi_matrix F B.ψ hB.std hunr hnt _ A hA
    · exact GlobalTheory.T.weil_operator_for_unipotent_matrix F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weil_operator_for_weyl_element F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure⟩ :=
    hasOp_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    have hcoord : GlobalTheory.LatVac.locCo co v γ = spAct G (GlobalTheory.LatVac.locCo M.co v γ) :=
      locCo_eq M.co co G hGe v γ
    rw [hcoord, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnity
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefRoot

theorem coef_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  intro D G _ _ Pl0 T m A cR cL lR lL B pl S Qt tauL lamR lamL gramR gramR' c0R c0R' c0L c0L' h h' i
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (lamL i)) with hs | hs
  · exact ⟨1, ⟨1, one_ne_zero, one_pow _⟩, fun F => by rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]⟩
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL i A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h'.coefL i A.μ0
  let g : Module.End D.what₂.LL (VV D.what₂.LL (lamL i)) := (e₂.symm.trans e).toLinearMap
  have hcg : ∀ v, c0L' i v = c0L i (g v) := fun v => by
    have h1 := hco₂ (e₂.symm v)
    rw [e₂.apply_symm_apply] at h1
    rw [← h1, hco]
    rfl
  have hinj : Function.Injective (c0L i) :=
    GlobalTheory.GalLift.rescale_inj (bVV D.what₂.LL (lamL i)) D.what₂.embLL (c0L i) (h.mapL i).2.1
  have hcomm : ∀ (γ : GQ (D.sp.V ((i : ℕ) + 1))) (γE : GL (Fin (D.sp.V ((i : ℕ) + 1)).rank) D.host.E),
      Bridge.IsRatMat _ γ γE → ∀ v, g (rhoVr tauL (lamL i) γE v) = rhoVr tauL (lamL i) γE (g v) := by
    intro γ γE hγ v
    apply hinj
    rw [← hcg, (h'.mapL i).1 γ γE hγ, hcg, (h.mapL i).1 γ γE hγ]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CoefSchur.endo_scalar D.what₂.LL (lamL i) g (_root_.GlobalTheory.RatDenseEnd.comm_all D _ tauL h.tauL_ok (lamL i) g hcomm)
  have hea : ∀ x, e x = a • e₂ x := fun x => by
    have h1 := ha (e₂ x)
    simpa [g] using h1
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (A.MtCSD i A.μ0).bV.index_nonempty
  have hx0 := (A.MtCSD i A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((A.MtCSD i A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    GlobalTheory.CoefUniq.mem_of_coords _ (bVV D.what₂.LL (lamL i)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hst : star a * a = 1 := by
    have hinj' := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (B.L i A.μ0).pres.coef_li
    have hp0 := GlobalTheory.CoefUniq.pair_ne_zero D.what₂.embLL _ hinj' _ (B.L i A.μ0).pres.coef_pair hx0
    refine GlobalTheory.CoefUniq.star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((B.L i A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice tauL (lamL i) _
      (GlobalTheory.CoefUniq.isFullLattice_hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl))
    refine GlobalTheory.CoefUniq.isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · let M := fun τ => dualFr (tauLat tauL τ (Bridge.hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl)))
      have hM : ∀ τ, Submodule.IsFullLattice D.what₂.LL (M τ) := fun τ =>
        dualFr_tauLat_isLattice tauL τ _
          (GlobalTheory.CoefUniq.isFullLattice_hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl))
      obtain ⟨d, hd, -, hd2⟩ := nb_global (nb_comm_nab (lamL i)) M hM
      have hd' : algebraMap (𝓞 D.what₂.LL) D.what₂.LL d ≠ 0 := by
        rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
      have h1 : Submodule.span D.what₂.LL (nabAtr tauL (lamL i) (Bridge.hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl)) : Set (VV D.what₂.LL (lamL i))) = ⊤ := by
        apply Submodule.map_injective_of_injective (f := (VV D.what₂.LL (lamL i)).subtype) (VV D.what₂.LL (lamL i)).injective_subtype
        rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨x, -, rfl⟩
          exact x.2
        · refine le_trans (le_of_eq (nb_VV_eq_bid (lamL i))) ?_
          rw [Submodule.span_le]
          intro P hP
          have hP1 : P ∈ nabStd D.what₂.LL (lamL i) := by
            rw [nb_nabStd_eq]
            exact Submodule.subset_span hP
          have hP2 := hd2 P hP1
          have hP3 : d • P ∈ VV D.what₂.LL (lamL i) := nb_le_VV (nb_comm_nab (lamL i)) M hM _ hP2
          have hP4 : d • P ∈ Submodule.span D.what₂.LL ((VV D.what₂.LL (lamL i)).subtype ''
              (nabAtr tauL (lamL i) (Bridge.hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl)) : Set (VV D.what₂.LL (lamL i)))) :=
            Submodule.subset_span ⟨⟨d • P, hP3⟩, hP2, rfl⟩
          have := Submodule.smul_mem _ (algebraMap (𝓞 D.what₂.LL) D.what₂.LL d)⁻¹ hP4
          rwa [nb_osmul, smul_smul, inv_mul_cancel₀ hd', one_smul] at this
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := GlobalTheory.CoefUniq.pow_eq_one_of_cmMax hm hst hi
  exact ⟨a, ⟨n, hn, han⟩, fun F => by rw [hcg, ha, LinearMap.map_smulₛₗ]⟩

end GlobalTheory.CoefRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZero
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffNonvanish

open MvPolynomial

theorem exists_coefFn_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  intro D n lam
  refine ⟨⟨Formalism.L2.Col.extVV D.what₂.LL lam, Formalism.L2.Col.extVV_mem D.what₂.LL lam⟩, ?_⟩
  by_contra h
  push_neg at h
  have hmap : MvPolynomial.map D.what₂.embLL (Formalism.L2.Col.extVV D.what₂.LL lam) = 0 := by
    refine GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam _ ?_
    intro x
    have hx := h x
    simp only [coefFn] at hx ⊢
    rw [eval₂Hom_map_hom] at *
    simpa using hx
  exact Formalism.L2.Col.extVV_ne_zero D.what₂.LL lam
    ((map_eq_zero_iff _ (MvPolynomial.map_injective _ D.what₂.embLL.injective)).mp hmap)

end GlobalTheory.CoeffNonvanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPairStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localChart_inertPlace_unitaryPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  first | exact @GlobalTheory.InertBridge.exists_chart | exact GlobalTheory.InertBridge.exists_chart | (intros; apply GlobalTheory.InertBridge.exists_chart <;> assumption)
end

