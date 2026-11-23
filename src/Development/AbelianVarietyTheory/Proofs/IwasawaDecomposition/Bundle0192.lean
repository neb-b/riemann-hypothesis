module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0024
public import Formalism.LocalToGlobal.Columns.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0180

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightVectorTransfer
section
open Matrix GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.JointHarm.OrbitMap

variable {ι : Type} {n : ℕ}

theorem one_mem_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by simp⟩

theorem one_mem_KC (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem K_sub_KC {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ GlobalTheory.Dec.KC ε :=
  ⟨⟨Unitary.toUnits ⟨g, hg.1⟩, rfl⟩, hg.2⟩

theorem mul_mem_K {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    (hh : h ∈ Formalism.REAL.Kset ε) : g * h ∈ Formalism.REAL.Kset ε :=
  ⟨mul_mem hg.1 hh.1, by rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]⟩

theorem star_mem_K {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    gᴴ ∈ Formalism.REAL.Kset ε := by
  have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
  have h2 : g * gᴴ = 1 := Unitary.mul_star_self_of_mem hg.1
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  calc gᴴ * Formalism.REAL.Jm ε = gᴴ * (Formalism.REAL.Jm ε * g) * gᴴ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * gᴴ := by
        rw [← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem single_mem_KC {ε : ι → Fin n → Bool} {τ : ι} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.Dec.KC (ε τ)) (σ : ι) :
    (Pi.mulSingle τ g : ι → Matrix (Fin n) (Fin n) ℂ) σ ∈ GlobalTheory.Dec.KC (ε σ) := by
  by_cases h : σ = τ
  · subst h; simpa using hg
  · simpa [h] using one_mem_KC _

theorem single_comm {τ : ι} (g : Matrix (Fin n) (Fin n) ℂ) {v : ι → Matrix (Fin n) (Fin n) ℂ}
    (hv : v τ = 1) : Pi.mulSingle τ g * v = v * Pi.mulSingle τ g := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [hv]
  · simp [h]

theorem fam_induction [Fintype ι] {ε : ι → Fin n → Bool} (Q : (ι → Matrix (Fin n) (Fin n) ℂ) → Prop)
    (h1 : Q 1)
    (hs : ∀ τ k v, k ∈ Formalism.REAL.Kset (ε τ) → (∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) → v τ = 1 → Q v →
      Q (Pi.mulSingle τ k * v)) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) : Q u := by
  have key : ∀ s : Finset ι, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ,
      (∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) → (∀ σ ∉ s, u σ = 1) → Q u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro u _ h
      have : u = 1 := funext fun σ => h σ (by simp)
      rw [this]; exact h1
    | insert τ s _ ih =>
      intro u hu h
      have hv : ∀ σ, Function.update u τ 1 σ ∈ Formalism.REAL.Kset (ε σ) := by
        intro σ
        by_cases e : σ = τ
        · subst e; simpa using one_mem_K _
        · simpa [e] using hu σ
      have e : u = Pi.mulSingle τ (u τ) * Function.update u τ 1 := by
        funext σ
        by_cases e : σ = τ
        · subst e; simp
        · simp [e]
      rw [e]
      refine hs τ _ _ (hu τ) hv (by simp) (ih _ hv fun σ hσ => ?_)
      by_cases e : σ = τ
      · subst e; simp
      · simpa [e] using h σ (by simp [e, hσ])
  exact key Finset.univ u hu (by simp)

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P} {ε : ι → Fin n → Bool} {μ : ι → Fin n → ℝ}

theorem adj_fam [Fintype ι] (h : IsHolFam ε B ϖ) (u : ι → Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b) := by
  refine fam_induction (ε := ε) (fun u => ∀ a b, B (ϖ u a) b = B a (ϖ (fun σ => (u σ)ᴴ) b)) ?_ ?_ u hu
  · intro a b
    have : (fun σ => ((1 : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) = 1 := by funext σ; simp
    rw [this, h.2.1]; rfl
  · intro τ k v hk hv _ ih a b
    have e : (fun σ => ((Pi.mulSingle τ k * v : ι → Matrix (Fin n) (Fin n) ℂ) σ)ᴴ) =
        (fun σ => (v σ)ᴴ) * Pi.mulSingle τ kᴴ := by
      funext σ
      by_cases e : σ = τ
      · subst e; simp
      · simp [e]
    rw [e, h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hv σ))) (single_mem_KC (K_sub_KC (star_mem_K hk))),
      Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (h.2.2.2 τ).2.2.2.1 k (K_sub_KC hk) _ _

theorem bottom_move (h : IsHolFam ε B ϖ) {x : P} (hx : IsBotFam ε ϖ μ x) {τ : ι}
    {v : ι → Matrix (Fin n) (Fin n) ℂ} (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) (hτ : v τ = 1) :
    IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) (ϖ v x) := by
  have c : ∀ g ∈ GlobalTheory.Dec.KC (ε τ), ϖ (Pi.mulSingle τ g) (ϖ v x) = ϖ v (ϖ (Pi.mulSingle τ g) x) := by
    intro g hg
    rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      ← h.2.2.1 _ _ (single_mem_KC hg) (fun σ => K_sub_KC (hv σ)),
      ← h.2.2.1 _ _ (fun σ => K_sub_KC (hv σ)) (single_mem_KC hg), single_comm g hτ]
  refine ⟨fun g hg hl => ?_, fun θ => ?_⟩
  · show ϖ (Pi.mulSingle τ g) (ϖ v x) = _
    rw [c g hg]
    exact congrArg _ ((hx τ).1 g hg hl)
  · show ϖ (Pi.mulSingle τ _) (ϖ v x) = _
    rw [c, ← map_smul]
    · exact congrArg _ ((hx τ).2 θ)
    · refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _

variable {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ}
  {ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P'}

theorem coef_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ)) :
    B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x') := by
  have hc : B' x' x' ≠ 0 := fun e => h0 (h'.1 _ e)
  refine fam_induction (ε := ε) (fun u => B x (ϖ u x) * B' x' x' = B x x * B' x' (ϖ' u x')) ?_ ?_ u hu
  · show B x (ϖ 1 x) * B' x' x' = B x x * B' x' (ϖ' 1 x')
    rw [h.2.1, h'.2.1]; rfl
  · intro τ k v hk hv hτ ih
    have e1 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P B _ P' B' _ x (ϖ v x) x' x' (h.2.2.2 τ) (h'.2.2.2 τ)
      (hx τ) (bottom_move h hx hv hτ) (hx' τ) (hx' τ) k hk
    have e2 := GlobalTheory.JointHarm.Sph.coeff_eq n (ε τ) (μ τ) P' B' _ P' B' _ x' (ϖ' v x') x' x' (h'.2.2.2 τ) (h'.2.2.2 τ)
      (hx' τ) (bottom_move h' hx' hv hτ) (hx' τ) (hx' τ) k hk
    show B x (ϖ (Pi.mulSingle τ k * v) x) * B' x' x' = B x x * B' x' (ϖ' (Pi.mulSingle τ k * v) x')
    rw [h.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      h'.2.2.1 _ _ (single_mem_KC (K_sub_KC hk)) (fun σ => K_sub_KC (hv σ)),
      Module.End.mul_apply, Module.End.mul_apply]
    apply mul_right_cancel₀ hc
    linear_combination (B' x' x') * e1 - (B x x) * e2 + (B' x' (ϖ' (Pi.mulSingle τ k) x')) * ih

theorem gram_fam [Fintype ι] (h : IsHolFam ε B ϖ) (h' : IsHolFam ε B' ϖ') {x : P} {x' : P'}
    (hx : IsBotFam ε ϖ μ x) (hx' : IsBotFam ε ϖ' μ x') (h0 : x' ≠ 0)
    (u v : ι → Matrix (Fin n) (Fin n) ℂ) (hu : ∀ σ, u σ ∈ Formalism.REAL.Kset (ε σ))
    (hv : ∀ σ, v σ ∈ Formalism.REAL.Kset (ε σ)) :
    B (ϖ u x) (ϖ v x) * B' x' x' = B x x * B' (ϖ' u x') (ϖ' v x') := by
  rw [adj_fam h u hu, adj_fam h' u hu, ← Module.End.mul_apply, ← Module.End.mul_apply,
    ← h.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ)),
    ← h'.2.2.1 _ _ (fun σ => K_sub_KC (star_mem_K (hu σ))) (fun σ => K_sub_KC (hv σ))]
  exact coef_fam h h' hx hx' h0 _ fun σ => mul_mem_K (star_mem_K (hu σ)) (hv σ)

theorem exists_map_of_gram {U : Type} (f : U → P) (f' : U → P') (hB : ∀ y, B y y = 0 → y = 0)
    {c d : ℂ} (hc : c ≠ 0) (hg : ∀ u v, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u, ψ (f' u) = f u := by
  first
  | exact @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram
  | (apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GramLinearMap.exists_linearMap_of_gram ..)

theorem exists_orbit_map : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  intro ι _ n ε μ P _ _ B ϖ P' _ _ B' ϖ' x x' h h' hx hx' h0
  obtain ⟨ψ, hψ⟩ := exists_map_of_gram (B := B) (B' := B')
    (U := {u : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)})
    (fun u => ϖ u.1 x) (fun u => ϖ' u.1 x') h.1 (fun e => h0 (h'.1 _ e))
    (fun u v => gram_fam h h' hx hx' h0 u.1 v.1 u.2 v.2)
  exact ⟨ψ, fun u hu => hψ ⟨u, hu⟩⟩

end GlobalTheory.JointHarm.OrbitMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEqui
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Classical in
theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add (f := _)]; exact a.add a'
    · simp only [map_add (f := _), Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), c, c']; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubMemIdS
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertNbr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IdemOf (F : Type) [Field F] [NumberField F] [Algebra F E] (Q : Pl E) (ε : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ε * ε = ε ∧ ∀ x : 𝓞 E, x ≠ 0 → (x ∈ Q.asIdeal ↔ ε * iA F E ((x : E)⁻¹) ∉ Formalism.L2.Herm.intAf F E)

namespace IdemOf

variable {Q : Pl E} {ε : E ⊗[F] Formalism.L2.Herm.Af F} (h : IdemOf F Q ε)
include h

theorem div_mem {t : 𝓞 E} (ht : t ∉ Q.asIdeal) : ε * iA F E ((t : E)⁻¹) ∈ Formalism.L2.Herm.intAf F E := by
  have t0 : t ≠ 0 := fun h0 => ht (h0 ▸ Q.asIdeal.zero_mem)
  by_contra hn
  exact ht ((h.2 t t0).2 hn)

theorem mem : ε ∈ Formalism.L2.Herm.intAf F E := by
  have := h.div_mem (one_notMem Q)
  simpa using this

theorem one_sub_mem : 1 - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) h.mem

theorem mul_one_sub : ε * (1 - ε) = 0 := by rw [mul_sub, h.1, mul_one, sub_self]

theorem mul_mem_of_val {x : E} (hx : Q.valuation E x ≤ 1) : ε * iA F E x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨a, t, ht, e⟩ := qsp_frac Q x hx
  have t0 : (t : E) ≠ 0 := fun h0 => ht (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e2 : x = (t : E)⁻¹ * algebraMap (𝓞 E) E a := by
    rw [← e]; field_simp
  rw [e2, map_mul, ← mul_assoc]
  exact mul_mem (h.div_mem ht) (iA_mem a)

theorem resS_eq_zero {w : Pl E} (hw : w ≠ Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : ε * a ∈ Formalism.L2.Herm.intAf F E) :
    resS F w ⟨ε * a, ha⟩ = 0 := by
  obtain ⟨t, htw, htQ⟩ : ∃ t ∈ w.asIdeal, t ∉ Q.asIdeal := by
    by_contra hn
    push Not at hn
    exact hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le Q.isPrime.ne_top hn))
  have t0 : (t : E) ≠ 0 := fun h0 => htQ (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have e : (⟨ε * a, ha⟩ : Formalism.L2.Herm.intAf F E) = oToS F E t * (⟨_, h.div_mem htQ⟩ * ⟨ε * a, ha⟩) := by
    apply Subtype.ext
    show ε * a = iA F E (t : E) * (ε * iA F E ((t : E)⁻¹) * (ε * a))
    have : iA F E (t : E) * iA F E ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ t0, map_one]
    linear_combination (-(ε * a) * ε) * this - a * h.1
  rw [e, map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htw, zero_mul]

omit h in
theorem val_unif {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) :
    Q.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
  rw [show (ϖ : E) = algebraMap (𝓞 E) E ϖ from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (Q.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have a2 := (Q.intValuation_le_pow_iff_mem ϖ 2).not.2 h2
  have h0 : Q.intValuation ϖ ≠ 0 := fun h0 => a2 (by rw [h0]; exact zero_le)
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at a1 a2
  omega

omit h in
theorem unif_ne {ϖ : 𝓞 E} (h2 : ϖ ∉ Q.asIdeal ^ 2) : (ϖ : E) ≠ 0 := fun h0 =>
  h2 (by rw [RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)

theorem div_pow_mem {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) {a : Formalism.L2.Herm.intAf F E}
    (ha : a ∈ idS F (Q.asIdeal ^ m)) :
    ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine Submodule.span_induction
    (p := fun (a : Formalism.L2.Herm.intAf F E) _ => ε * iA F E (((ϖ : E) ^ m)⁻¹) * (a : E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨p, hp, rfl⟩
    rw [← iA_coe, mul_assoc, ← map_mul]
    refine h.mul_mem_of_val ?_
    have a1 := (Q.intValuation_le_pow_iff_mem p m).2 hp
    rw [map_mul, map_inv₀, map_pow, val_unif h1 h2, HeightOneSpectrum.valuation_of_algebraMap, ← WithZero.exp_nsmul,
      inv_mul_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), mul_one]
    simpa using a1
  · simp
  · intro a b _ _ ha hb
    rw [Subring.coe_add, mul_add]; exact add_mem ha hb
  · intro c a _ ha
    rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem c.2 ha

theorem one_sub_mem_idS [StarRing E] (m : ℕ) : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) ∈ idS F (Q.asIdeal ^ m) := by
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ Q.asIdeal Q.ne_bot Q.isPrime.ne_top 1
  rw [pow_one] at h1
  have hi : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨ε, h.mem⟩ = 0 :=
    Subtype.ext (by show (1 - ε) * ε = 0; rw [mul_comm, h.mul_one_sub])
  have h3 : resS F Q ⟨1 - ε, h.one_sub_mem⟩ = 0 := by
    have := congrArg (resS F Q) hi
    rw [map_mul, map_zero] at this
    refine (mul_eq_zero.1 this).resolve_right fun h0 => ?_
    have h4 := h.div_pow_mem h1 h2 1 (a := ⟨ε, h.mem⟩) (by rw [pow_one]; exact mem_idS_of_resS h0)
    have ϖ0 : ϖ ≠ 0 := fun h0 => h2 (h0 ▸ zero_mem _)
    refine (h.2 ϖ ϖ0).1 h1 ?_
    rwa [pow_one, mul_right_comm, h.1] at h4
  have h5 := Ideal.pow_mem_pow (mem_idS_of_resS h3) m
  have h6 : (⟨1 - ε, h.one_sub_mem⟩ : Formalism.L2.Herm.intAf F E) * ⟨1 - ε, h.one_sub_mem⟩ = ⟨1 - ε, h.one_sub_mem⟩ :=
    Subtype.ext (by show (1 - ε) * (1 - ε) = 1 - ε; linear_combination h.1)
  rcases m with _ | m
  · unfold idS
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial
  · rw [IsIdempotentElem.pow_succ_eq m h6] at h5
    unfold idS at h5 ⊢
    rwa [Ideal.map_pow]

theorem mem_idS_pow_iff [StarRing E] {ϖ : 𝓞 E} (h1 : ϖ ∈ Q.asIdeal) (h2 : ϖ ∉ Q.asIdeal ^ 2) (m : ℕ) (a : Formalism.L2.Herm.intAf F E) :
    a ∈ idS F (Q.asIdeal ^ m) ↔ ε * iA F E (((ϖ : E) ^ m)⁻¹) * a ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨h.div_pow_mem h1 h2 m, fun ha => ?_⟩
  have e : a = oToS F E (ϖ ^ m) * ⟨_, ha⟩ + ⟨1 - ε, h.one_sub_mem⟩ * a := by
    apply Subtype.ext
    show (a : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * (ε * iA F E (((ϖ : E) ^ m)⁻¹) * a) + (1 - ε) * a
    have : iA F E (algebraMap (𝓞 E) E (ϖ ^ m)) * iA F E (((ϖ : E) ^ m)⁻¹) = 1 := by
      rw [← map_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ (unif_ne h2)), map_one]
    linear_combination (-(ε * (a : E ⊗[F] Formalism.L2.Herm.Af F))) * this
  rw [e]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow h1 m)))
    (Ideal.mul_mem_right _ _ (h.one_sub_mem_idS m))

end IdemOf

end GlobalTheory.InertNbr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain

namespace GlobalTheory.Chain.InnerSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theta_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1 (fun k f hf => ⟨?_, rfl⟩) f hf P).1
  obtain ⟨τ, i, j⟩ := k
  exact GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.Chain.InnerSteps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.QuotVol

theorem quot_volume_ne_zero_ne_top : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    IsQuot V μ 𝓕 → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := fun D V μ 𝓕 h =>
  ⟨((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram μ h.1).2
      𝓕 𝓕 h.2 h.2).2,
    (GlobalTheory.Mem.VolFin.finVol D.host.F D.host.E D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram
      (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) μ h.1 𝓕 h.2).ne⟩

end GlobalTheory.Mem.QuotVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolume
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volTieG_of_trueVol : ∀ D : D7, letI := D.host.cmStar;
    (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  intro D
  letI := D.host.cmStar
  intro h
  rw [volTieG_iff]
  intro W hW
  rw [h W]
  exact _root_.GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ _ D.cd W (isCMFam_host _ D.host _ D.eTau) hW

end GlobalTheory.Mem.Vol
end

