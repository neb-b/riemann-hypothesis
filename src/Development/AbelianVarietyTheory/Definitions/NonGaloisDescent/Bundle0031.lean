module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspSubsetBaseForms
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead.Test

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_apply (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) (g : GA D (T.V j σ)) :
    C.rd a f₂ g = C.cc₂ (C.dict₂ g).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g *
      rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) := by
  simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
  ring

theorem zero_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : 0 ∈ C.ratForms a n := by
  refine ⟨0, ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩, ?_⟩
  funext g
  rw [rd_apply, map_zero]
  simp

theorem add_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {φ ψ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ C.ratForms a n) (hψ : ψ ∈ C.ratForms a n) : φ + ψ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  obtain ⟨f', hf', rfl⟩ := hψ
  refine ⟨f + f', ⟨Submodule.add_mem _ hf.1 hf'.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hf.2 hf'.2⟩, ?_⟩
  funext g
  simp only [Pi.add_apply, rd_apply, map_add (f := _)]
  ring

theorem smul_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ C.ratForms a n) : C.σ₂ x • φ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  refine ⟨x • f, ⟨Submodule.smul_mem _ _ hf.1, by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩, ?_⟩
  funext g
  simp only [Pi.smul_apply, rd_apply, map_smulₛₗ, smul_eq_mul]
  ring

end GlobalTheory.CoverRead.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem Frame.Good.posDef {F : Frame S T} (h : F.Good) (τ : D.what₂.Tau) : (gramAt D S τ).PosDef := by
  have := (GlobalTheory.GalLift.Vec.isCartanInv_one (h.onbS τ)).2.2
  rwa [Matrix.mul_one] at this

theorem exists_isClassSystem (B : Base S T) (hF : B.F.Good) (ψ : Twist D Circle) :
    ∃ (m : ℕ) (h : Fin m → GA D S), IsClassSystem S (B.levJ ψ) h := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover S hF.posDef (B.levJ ψ)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev S B.F.βS (B.levS ψ))
  have hl : ∀ x : Bridge.Gf S, ∃ k ∈ GfC S, finPt S k = x := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk, e⟩ := GlobalTheory.LevelOpen.exists_finPart D S g
    exact ⟨k, hk, Subtype.ext e⟩
  choose l hl1 hl2 using hl
  have hr : Equivalence fun g g' : Bridge.Gf S => ∃ (γ : GQ S) (k : B.levJ ψ), g = Bridge.ratF S γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr c
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.ParahoricCompact.exists_compact_entries B.F.βS
  refine ⟨n, fun a => l (c (f a)), fun a => hl1 _, fun g => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := hc g
    simp only [hl2]
    exact hf g a ha
  · exact GlobalTheory.RepsObj.finite_stab S hF.posDef _ hC (fun k hk => hCe k.1 (Base.mem_St_of_mem_levJ hk)) _

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivCoefNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct ComplexOrder

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.AdjDatumNe

theorem pair_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → E)
    (hu : ∀ y ∈ Λ, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = ∑ k, u k * y k)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ∑ k, (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * z k ∈ Formalism.L2.Herm.intAf F E := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hu y hy
    have hm : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.intAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
    convert hm using 1
    rw [hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (u k ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y k ⊗ₜ[F] 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hx hy
  | smul c x _ hx =>
    have := mul_mem c.2 hx
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ * (c.1 * x k) = _
    ring

def ct {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) : Matrix (Fin b) (Fin a) (EAf D) := (A.map (cF D))ᵀ

theorem ct_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin c) (EAf D)) :
    ct (A * B) = ct B * ct A := by
  rw [ct, Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem ct_map {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : ct (A.map (eToEAf D)) = Aᴴ.map (eToEAf D) := rfl

theorem int_ct {a b : ℕ} {A : Matrix (Fin a) (Fin b) (EAf D)} (h : IsIntM A) : IsIntM (ct A) :=
  fun i j => cF_mem_int (h j i)

theorem int_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) (EAf D)} {B : Matrix (Fin b) (Fin c) (EAf D)} (h : IsIntM A)
    (h' : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun p _ => mul_mem (h i p) (h' p j)

theorem gram_frame_int (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (EAf D)}
    (hV : IsSelfDualC V Λ) (f : IsFrame β Λ) :
    IsIntM (ct β.val * V.gram.map (eToEAf D) * β.val) ∧
      IsIntM ((β⁻¹).val * (V.gram⁻¹).map (eToEAf D) * ct (β⁻¹).val) := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hV
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin V.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin V.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * V.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have hG : V.gramᴴ = V.gram := Matrix.ext fun i j => GlobalTheory.LatVac.gram_star V j i
  have hcol : ∀ a, (fun k => β.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := fun a => by
    refine (f _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k a) i = ((β⁻¹).val * β.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : ∀ t : Fin n → Fin V.rank → D.host.E, (∀ k, t k ∈ Λ) →
      IsIntM (((Matrix.of fun a k => t k a)ᴴ * V.gram).map (eToEAf D) * β.val) := fun t ht k a => by
    refine pair_int Λ (fun j => ((Matrix.of fun a k => t k a)ᴴ * V.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hV.2 y).1 hy _ (ht k)
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : ∀ t : Fin n → Fin V.rank → D.host.E, (∀ k, t k ∈ Λ) →
      IsIntM ((β⁻¹).val * (Matrix.of fun a k => t k a).map (eToEAf D)) := fun t ht a k =>
    (f _).1 (pure_mem_hatL Λ 1 (one_mem _) _ (ht k)) a
  constructor
  · have := int_mul (int_ct (i1 s fun k => (hs k).1)) (i1 s' fun k => (hs k).2)
    rw [← hs₁, ← hs₂, ct_mul, ct_map, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ β.val, ← Matrix.map_mul, Matrix.mul_assoc V.gram, e1, Matrix.mul_one] at this
    rwa [Matrix.mul_assoc]
  · have := int_mul (i2 s fun k => (hs k).1) (int_ct (i2 s' fun k => (hs k).2))
    rw [← hs₁, ← hs₂, ct_mul, ct_map, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (ct _), ← Matrix.map_mul] at this
    rwa [Matrix.inv_eq_left_inv (B := s₁ * s₂ᴴ) (by rw [Matrix.mul_assoc, e1]), Matrix.mul_assoc]

theorem int_adj_of_int {F : Frame S T} (hF : F.Good) {x : WO S T} (h : IsIntM (frMapO S T F.βS F.βT x)) :
    IsIntM (frMapAdj S T F.βS F.βT x) := by
  have e : x.map (toEAf D) = F.βT.val * frMapO S T F.βS F.βT x * (F.βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hF.sdS hF.frS).2 (int_ct h)) (gram_frame_int T hF.sdT hF.frT).1
  rw [frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this


end GlobalTheory.ExportSeries.Model

end
end

