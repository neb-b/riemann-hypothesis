module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSympl

variable {D : D7}

theorem conj_conj (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_ι (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem conj_ι_mul_ι (p : Place D k) (u v : k) : cA D (p.ι u) * p.ι v = 0 := by
  calc cA D (p.ι u) * p.ι v = cA D (p.e * p.ι u) * (p.e * p.ι v) := by rw [e_mul_ι, e_mul_ι]
    _ = (p.e * cA D p.e) * (cA D (p.ι u) * p.ι v) := by rw [map_mul]; ring
    _ = 0 := by rw [p.split.2.1, zero_mul]

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem up_half (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    IsHalf p.e (p.up FS FT x) := fun i j => e_mul_ι p _

theorem down_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  have hm : ((FT.β * x * FS.γ).map p.ι).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  unfold Place.down Place.up
  rw [hm, show FT.γ * (FT.β * x * FS.γ) * FS.β = (FT.γ * FT.β) * x * (FS.γ * FS.β) by simp only [Matrix.mul_assoc],
    FT.γβ, FS.γβ, Matrix.one_mul, Matrix.mul_one]

theorem up_down (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (z : WO S T)
    (hz : IsHalf p.e z) : p.up FS FT (p.down FS FT z) = z := by
  unfold Place.down Place.up
  rw [show FT.β * (FT.γ * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ
      = (FT.β * FT.γ) * (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * (FS.β * FS.γ) by
      simp only [Matrix.mul_assoc], FT.βγ, FS.βγ, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply]
  rw [p.ι_π]
  exact hz i j

theorem hO_up_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x y : Matrix Y Y' k) :
    hO S T (p.up FS FT x) (p.up FS FT y) = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  show incA D _ * cA D (p.ι _) * incA D _ * p.ι _ = 0
  rw [show ∀ A B C E' : AE D, A * C * B * E' = A * B * (C * E') from fun _ _ _ _ => by ring, conj_ι_mul_ι, mul_zero]

theorem e_mul_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (y : WO S T) : p.e * hO S T (p.up FS FT t) y = hO S T (p.up FS FT t) y := by
  have key : ∀ (A B C : AE D) (u : k), p.e * (A * B * C * p.ι u) = A * B * C * p.ι u := fun A B C u => by
    calc p.e * (A * B * C * p.ι u) = A * B * C * (p.e * p.ι u) := by ring
      _ = _ := by rw [e_mul_ι]
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  exact key _ _ _ _

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem psi_sympl_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)
    (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle) (hχ : p.IsChar ψ ψk) (t : Matrix Y Y' k) (y : WO S T) :
    ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y)) := by
  rw [hχ, p.ι_π, e_mul_hO_up]
  rfl

theorem sum_four_eq_trace_mul {m n : Type} [Fintype m] [Fintype n] (A : Matrix m m k) (N : Matrix m n k) (B : Matrix n n k)
    (X : Matrix n m k) : ∑ a, ∑ b, ∑ c, ∑ d, A a b * N b c * B c d * X d a = Matrix.trace (A * N * B * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem pi_hO_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : Matrix Y Y' k)
    (N : Matrix (Fin S.rank) (Fin T.rank) k) :
    p.π (hO S T (p.up FS FT t) (N.transpose.map fun a => cA D (p.ι a))) =
      Matrix.trace ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ)) := by
  unfold hO
  rw [← sum_four_eq_trace_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul]
  have hterm : ∀ a b c d, p.π (incA D (S.gram⁻¹ a b)) * p.π (cA D ((N.transpose.map fun a => cA D (p.ι a)) c b)) *
      p.π (incA D (T.gram c d)) * p.π (p.up FS FT t d a) =
      (S.gram⁻¹).map (p.π.comp (incA D)) a b * N b c * T.gram.map (p.π.comp (incA D)) c d * (FT.β * t * FS.γ) d a := by
    intro a b c d
    simp only [Matrix.map_apply, Matrix.transpose_apply, conj_conj, p.π_ι, Place.up, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => hterm a b c d

theorem exists_pairing (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (b : Matrix Y Y' k) :
    ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set f := p.π.comp (incA D)
  set N : Matrix (Fin S.rank) (Fin T.rank) k := S.gram.map f * FS.β * b.transpose * FT.γ * (T.gram⁻¹).map f
  refine ⟨N.transpose.map fun a => cA D (p.ι a), fun i j => ?_, fun t => ?_⟩
  · show cA D p.e * cA D (p.ι _) = cA D (p.ι _)
    rw [← map_mul, e_mul_ι]
  · rw [pi_hO_up]
    have hA : (S.gram⁻¹).map f * S.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.map_one _ (map_zero f) (map_one f)]
    have hB : (T.gram⁻¹).map f * T.gram.map f = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit T), Matrix.map_one _ (map_zero f) (map_one f)]
    have hANB : (S.gram⁻¹).map f * N * T.gram.map f = FS.β * b.transpose * FT.γ := by
      simp only [N, Matrix.mul_assoc]
      rw [hB, Matrix.mul_one, ← Matrix.mul_assoc ((S.gram⁻¹).map f), hA, Matrix.one_mul]
    rw [hANB]
    rw [show FS.β * b.transpose * FT.γ * (FT.β * t * FS.γ) = FS.β * (b.transpose * (FT.γ * FT.β) * t * FS.γ) by
      simp only [Matrix.mul_assoc], FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm

end GlobalTheory.LocSympl

namespace GlobalTheory.LocSympl

theorem halves_at_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → (∀ x, IsHalf p.e (p.up FS FT x) ∧ p.down FS FT (p.up FS FT x) = x) ∧ (∀ z : WO S T, IsHalf p.e z → p.up FS FT (p.down FS FT z) = z) ∧ (∀ x y, symplO S T (p.up FS FT x) (p.up FS FT y) = 0) ∧ (∀ t (y : WO S T), IsHalf (cA D p.e) y → ψ (symplO S T (p.up FS FT t) y) = ψk (p.π (hO S T (p.up FS FT t) y))) ∧ ∀ b : Matrix Y Y' k, ∃ y : WO S T, IsHalf (cA D p.e) y ∧ ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ ψk hχ
  exact ⟨fun x => ⟨up_half p FS FT x, down_up p FS FT x⟩, fun z hz => up_down p FS FT z hz,
    fun x y => by unfold symplO; rw [hO_up_up, mul_zero, map_zero],
    fun t y _ => psi_sympl_up p FS FT ψ ψk hχ t y, fun b => exists_pairing p FS FT b⟩

end GlobalTheory.LocSympl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfEqRationalAddNsmulStandardHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.DenseHalf

theorem half_eq_rat_add_nsmul : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ M : ℕ, 0 < M → ∀ w : WO S T, IsHalf e w → ∃ (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ w = z.map (fun r => e * incA D r) + M • v := by
  intro D S T e P he M hM w hw
  obtain ⟨z, v, hv, hvh, h⟩ := GlobalTheory.AdForm.exists_rat_half_approx S T e P he M hM w
  refine ⟨z, -v, neg_mem hv, fun i j => ?_, ?_⟩
  · simp only [Matrix.neg_apply, mul_neg, hvh i j]
  · have hw' : e • w = w := by
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, hw i j]
    rw [h, hw', smul_neg]
    abel

end GlobalTheory.AdForm.DenseHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfLat
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P) {r : D.host.E}
    (hr : finPart D (e * incA D r) ∈ intAE D) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * r := by
  rcases (P.valuation D.host.E).val_le_one_or_val_inv_lt_one r with h | h
  · obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r h
    exact ⟨d, d.2, n, by rw [mul_comm]; exact hd.symm⟩
  by_cases hr0 : r = 0
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by simp [hr0]⟩
  obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r⁻¹ h.le
  have hdP : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h => hdP (h ▸ zero_mem _)
  have hd0' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  have hd' : r⁻¹ * ((d : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (inv_ne_zero hr0) hd0' hd'
  have hnP : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := D.host.E) n).1 ?_
    change P.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E n) < 1
    rw [← hd, Valuation.map_mul]
    exact mul_lt_one_of_lt_of_le h (P.valuation_le_one _)
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hdP ((he.2 _ hd0).2 h)
  refine absurd ?_ ((he.2 _ hn0).1 hnP)
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hr h1
  rwa [← RingHom.map_mul, mul_mul_mul_comm, he.1.1, ← RingHom.map_mul, ← inv_inv r, ← mul_inv, hd'] at h2

noncomputable def form (S : HSp D) (s : Fin S.rank → D.host.E) : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E :=
  ∑ i, ∑ j, (star (s i) * S.gram i j) • LinearMap.proj j

theorem form_apply (s v : Fin S.rank → D.host.E) : form S s v = ∑ i, ∑ j, star (s i) * S.gram i j * v j := by
  simp [form, LinearMap.sum_apply]

theorem expand {n : ℕ} {s s' : Fin n → Fin S.rank → D.host.E}
    (h : ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) (v : Fin S.rank → D.host.E) :
    v = ∑ k, form S (s' k) v • s k := by
  funext a
  have h1 : v a = ∑ j, (∑ i, s i a * ∑ k, star (s' i k) * S.gram k j) * v j := by simp [h]
  rw [h1, Finset.sum_apply]
  simp only [form_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def coefA (S T : HSp D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    WO S T →+ AE D :=
  AddMonoidHom.mk' (fun u => ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m) fun x y => by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem coefA_apply (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (u : WO S T) :
    coefA S T b s t u = ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m := rfl

theorem coefA_int (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {b : D.host.E}
    (hb : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b)
    {s : Fin S.rank → D.host.E} (hs : s ∈ N) {t : Fin T.rank → D.host.E} (ht : t ∈ N') {u : WO S T}
    (hu : u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    finPart D (coefA S T b s t u) ∈ intAE D := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s0, hs0, t0, ht0, rfl⟩ := hw
    obtain ⟨c, hc'⟩ := hb a ha
    obtain ⟨o, ho⟩ := (hN.2 s).1 hs s0 hs0
    obtain ⟨o', ho'⟩ := (hN'.2 t0).1 ht0 t ht
    refine AddSubgroup.subset_closure ⟨α, hα, c * o' * o, ?_⟩
    have h1 : ∀ x y : D.host.E, incA D x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * y) := fun x y => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, ∑ m, (b * (star (t i) * T.gram i j) * s m) *
        (a * t0 j * ∑ k, star (s0 k) * S.gram k m) := by
      have h3 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * o' * o := by
        simp only [map_mul]
      rw [h3, hc', ho, ho', Finset.sum_comm (f := fun i j => star (s0 i) * S.gram i j * s j), Finset.mul_sum (a := a * b),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum (a := a * b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      ring
    rw [coefA_apply]
    simp only [Matrix.of_apply, h1, ← TensorProduct.tmul_sum]
    rw [h2]
    rfl
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact neg_mem hx

theorem coefA_rat (e : AE D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E)
    (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    coefA S T b s t ((LinearMap.toMatrix' x).map fun r => e * incA D r) = e * incA D (b * form T t (x s)) := by
  rw [coefA_apply, form_apply, ← LinearMap.toMatrix'_mulVec x s]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.map_apply, mul_left_comm, ← RingHom.map_mul]
  congr 2
  ring


set_option maxHeartbeats 1000000 in
theorem mem_localization_of_component (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {e e' : AE D}
    {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e' P) (hee : e' * e = e')
    {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T N' hN'
  have hxe : x = ∑ k, ∑ i, form T (t' i) (x (s k)) • (form S (s' k)).smulRight (t i) := by
    refine LinearMap.ext fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [expand hss v, map_sum]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [map_smul, expand htt (x (s k)), Finset.smul_sum]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D)
  have h1 : (1 : D.host.E) ∈ D.host.AA0 * (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0]
    exact FractionalIdeal.one_mem_one _
  rw [← one_smul D.host.E x]
  refine FractionalIdeal.mul_induction_on (C := fun c => c • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
    (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) h1 (fun a ha b hb => ?_)
    fun a b ha hb => by rw [add_smul]; exact add_mem ha hb
  have hb' : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b := fun a ha => by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul] at ha
    have h := FractionalIdeal.mul_mem_mul ha hb
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0] at h
    exact (FractionalIdeal.mem_one_iff _).1 h
  have hi : finPart D e' ∈ intAE D := by
    by_contra h
    refine P.asIdeal.primeCompl.one_mem ((he.2 1 one_ne_zero).2 ?_)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one]
  rw [hxe, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hi (coefA_int hN hN' hb' (hs k).1 (ht i).2 hx)
  rw [coefA_rat, ← RingHom.map_mul, ← mul_assoc, hee] at h2
  obtain ⟨d, hd, o, ho⟩ := exists_den he h2
  refine ⟨d, hd, ?_⟩
  have h3 : a • (form S (s' k)).smulRight (t i) ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    refine Submodule.subset_span ⟨a, ha, _, fun v hv => ?_, rfl⟩
    obtain ⟨c, hc⟩ := (hN.2 v).1 hv _ (hs k).2
    rw [LinearMap.smulRight_apply, form_apply, ← hc]
    exact N'.smul_mem c (ht i).1
  convert Submodule.smul_mem _ o h3 using 1
  rw [← IsScalarTower.algebraMap_smul D.host.E d, ← IsScalarTower.algebraMap_smul D.host.E o,
    show algebraMap _ D.host.E o = _ from ho, smul_smul, smul_smul, smul_smul]
  congr 1
  change (d : D.host.E) * _ * _ = _
  ring

theorem comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (HalfPairing.toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.SplitScalar.infPart_splitIdem he.1
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem half_mem_latO_iff : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  intro D S T hc e SS he N N' hN hN' x
  constructor
  · intro hx P hP
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
    exact mem_localization_of_component hc hN hN' ha hae hx
  · intro hx
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    have e1 : ((LinearMap.toMatrix' x).map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x).map fun r => es PP * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    exact sum_mem fun PP hPP => comp_mem hc hN (hes PP hPP) (hx PP hPP)

end GlobalTheory.AdForm.HalfLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMulHeightPowOfBoundedFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.realZeta_integrable_mul_heightPow : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  intro G _ _ _ μ z m H C b t hz hm hH hpos htb hbound
  have hmeas : AEStronglyMeasurable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)) μ := by
    refine hz.aestronglyMeasurable.mul ?_
    exact ((Complex.measurable_ofReal.comp hH.measurable).pow_const _).aestronglyMeasurable
  refine Integrable.mono' (hm.norm.const_mul (max C 0)) hmeas ?_
  refine Filter.Eventually.of_forall (fun g => ?_)
  obtain ⟨h0, h1⟩ := hpos g
  have hre : (((0:ℝ):ℂ) - (t:ℂ)/2).re = -(t:ℝ)/2 := by simp; ring
  have hcpow : ‖((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)‖ = H g ^ (-(t:ℝ)/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h0, hre]
  rw [norm_mul, hcpow]
  have hw : 0 ≤ H g ^ (-(t:ℝ)/2) := Real.rpow_nonneg h0.le _
  have hprod : H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2) = H g ^ (((b:ℝ) - t)/2) := by
    rw [← Real.rpow_add h0]; ring_nf
  have htb' : (t:ℝ) ≤ b := by exact_mod_cast htb
  have hle1 : H g ^ (((b:ℝ) - t)/2) ≤ 1 := Real.rpow_le_one h0.le h1 (by linarith)
  have hnn : 0 ≤ H g ^ (((b:ℝ) - t)/2) := Real.rpow_nonneg h0.le _
  calc ‖z g‖ * H g ^ (-(t:ℝ)/2) ≤ C * H g ^ ((b:ℝ)/2) * ‖m g‖ * H g ^ (-(t:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (hbound g) hw
    _ = C * (H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2)) * ‖m g‖ := by ring
    _ = C * H g ^ (((b:ℝ) - t)/2) * ‖m g‖ := by rw [hprod]
    _ ≤ max C 0 * ‖m g‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc C * H g ^ (((b:ℝ) - t)/2) ≤ max C 0 * H g ^ (((b:ℝ) - t)/2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
          _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hle1 (le_max_right _ _)
          _ = max C 0 := mul_one _
end

