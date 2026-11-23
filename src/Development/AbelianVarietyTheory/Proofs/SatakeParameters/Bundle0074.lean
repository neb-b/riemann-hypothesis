module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BurnsideSub

theorem matRep_apply {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (g : Γ)
    (v : Fin a → k) :
    matRep ((Units.coeHom _).comp ρ) g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := by
  simp [matRep]

theorem isIrrSub_top_of_intertwine {K Γ : Type} [Field K] [Group Γ] {a d : ℕ}
    (ρ : Γ →* GL (Fin a) K) (σ : Γ →* GL (Fin d) K) (B : Matrix (Fin a) (Fin d) K)
    (C : Matrix (Fin d) (Fin a) K) (hCB : C * B = 1)
    (hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) K) * B = B * (σ g : Matrix (Fin d) (Fin d) K))
    (h : IsIrrSub ρ (LinearMap.range B.mulVecLin)) : IsIrrSub σ ⊤ := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    have := congrArg C.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCB] using this
  have hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) →
      IsInv ρ (U.map B.mulVecLin) := by
    rintro U hU g _ ⟨v, hv, rfl⟩
    refine ⟨_, hU g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  refine ⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩
  · rw [LinearMap.range_eq_map, h0, Submodule.map_bot]
  · have hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin := LinearMap.map_le_range
    rcases h.2.2 _ hle (hmap U hU) with h1 | h1
    · left
      exact Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)
    · right
      rw [LinearMap.range_eq_map] at h1
      exact Submodule.map_injective_of_injective hinj h1

theorem span_restrict_eq_top_of_absIrrSub : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W),
    AbsIrrSub ρ W →
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ a ρ W hW habs
  classical
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun

  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl

  let L : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' L
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = L c := fun c => LinearMap.toMatrix'_mulVec L c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  set f := algebraMap k (AlgebraicClosure k) with hf
  have hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  unfold AbsIrrSub at habs
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

end GlobalTheory.BurnsideSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory

namespace ThetaCosetSum

open Formalism.L2.Th1.H

theorem xiL_eq_kernel {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) *
      ∑ x ∈ SX, ∑ y ∈ SB, ∑ t ∈ SA, Φ (t - x) *
        (α x * ((SA.card : ℂ)⁻¹ * (brk H y t)⁻¹ * α y * opU H y e (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) := by
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [opU]
  simp only [xiS, sumU, hatS, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem sum_xiL {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (hv : 0 < vol)
    (SX SA SB : Finset V) (c : ι → ℂ) (Φ : ι → V → ℂ) (Ψ e : V → ℂ) (hΨ : ∀ t, Ψ t = ∑ i, c i * Φ i t) (z : V) :
    ∑ i, c i * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiL H α vol SX SA SB (Φ i) e z) = xiL H α 1 SX SA SB Ψ e z := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have h2 : ((vol : ℝ) : ℂ) = ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hv.le).symm
  have h3 : ∀ w : ℂ, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) * w) = w := by
    intro w
    generalize ((Real.sqrt vol : ℝ) : ℂ) = s at hs h2
    rw [h2]; field_simp
  simp only [xiL_eq_kernel, h3, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, hΨ, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]


open Classical in
theorem eq_sum_coset {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A B : Submodule R M) (hBA : B ≤ A)
    [Fintype (↥A ⧸ B.comap A.subtype)] (Ξ : M → ℂ) (h1 : ∀ x, Ξ x ≠ 0 → x ∈ A) (h2 : ∀ x, ∀ y ∈ B, Ξ (x + y) = Ξ x)
    (r : (↥A ⧸ B.comap A.subtype) → ↥A) (hr : ∀ q, Submodule.Quotient.mk (r q) = q) (t : M) :
    Ξ t = ∑ q, Ξ (r q) * (if t - (r q : M) ∈ B then 1 else 0) := by
  by_cases ht : t ∈ A
  · have key : ∀ q, t - (r q : M) ∈ B ↔ q = Submodule.Quotient.mk (⟨t, ht⟩ : ↥A) := by
      intro q
      rw [eq_comm]
      conv_rhs => rw [← hr q]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_eq_single (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A))]
    · have hm := (key _).mpr rfl
      rw [if_pos hm, mul_one, ← h2 (r (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A)) : M) _ hm, add_sub_cancel]
    · intro q _ hq
      rw [if_neg (fun h => hq ((key q).mp h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : Ξ t = 0 := by
      by_contra h
      exact ht (h1 t h)
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply ht
    have := A.add_mem (hBA h) (r q).2
    simpa using this

end ThetaCosetSum


open ThetaCosetSum in
theorem latSum_thInd_eq_thC : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndTieD a b S (cA * cB) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → 0 < volC A.AA S N N' → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → ∀ z, latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) (fun x => Ξ x * A.thInd S N N' cB x z) = thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) Ξ (A.e a b N N') z := by
  intro X A a b S N N' cA cB Ξ hT hN hN' hA hB hv hfin h1 h2 z
  classical
  let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  have hle : mulLat cB (homAt S N N') ≤ divLat cA (homAt S N N') := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy)
  have hdiv : ∀ x ∈ divLat cA (homAt S N N'), x ∈ divLat (cA * cB) (homAt S N N') := by
    intro x hx
    have h : (cB : 𝓞 X.E) • (cA : 𝓞 X.E) • x ∈ homAt S N N' := Submodule.smul_mem _ _ hx
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at h
    exact h
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)) with hr
  have hrq : ∀ q, Submodule.Quotient.mk (r q) = q := fun q => Function.surjInv_eq _ q
  have hx : ∀ q, A.thInd S N N' cB (r q : HomE X.E a b) z = _ := fun q =>
    hT N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, hdiv _ (r q).2⟩ (Nat.mul_pos hA hB) z
  simp only [hx]
  unfold xiC thC xiV
  refine sum_xiL _ _ _ hv _ _ _ (fun q => Ξ (r q)) (fun q => onV (X.embC A.σ₀) A.δ (cosInd S N N' cB (r q))) _ _ ?_ z
  intro v
  unfold onV
  split_ifs with h
  · have := eq_sum_coset _ _ hle Ξ h1 h2 r hrq h.choose
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cosInd
    congr
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingIntClosure
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.CompletedBasis

section General

variable {l : ℕ} [Fact l.Prime]

theorem isCompact_closure_range {A V : Type} [AddCommGroup A] [Module.Finite ℤ A] [NormedAddCommGroup V]
    [NormedSpace ℚ_[l] V] (f : A →+ V) : IsCompact (closure (Set.range f)) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let g : (Fin n → ℤ_[l]) → V := fun c => ∑ i, ((c i : ℤ_[l]) : ℚ_[l]) • f (b i)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have hc : IsCompact (Set.range g) := isCompact_range hg
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := hb ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ha
  refine ⟨fun i => (c i : ℤ_[l]), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [g, map_sum, map_zsmul, PadicInt.coe_intCast, Int.cast_smul_eq_zsmul]

variable {K : Type} [Field K] [NumberField K] (ρ : K →+* ℂ_[l])

def intClosure : Subring ℂ_[l] := (ρ.comp (algebraMap (𝓞 K) K)).range.topologicalClosure

theorem coe_intClosure : (intClosure ρ : Set ℂ_[l]) = closure (Set.range fun a : 𝓞 K => ρ (a : K)) := rfl

theorem isCompact_intClosure : IsCompact (intClosure ρ : Set ℂ_[l]) :=
  isCompact_closure_range (l := l) (ρ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom

theorem mem_intClosure (a : 𝓞 K) : ρ (a : K) ∈ intClosure ρ := subset_closure ⟨a, rfl⟩

theorem norm_le_one_of_mem {x : ℂ_[l]} (hx : x ∈ intClosure ρ) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := (isCompact_intClosure ρ).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC _ ((intClosure ρ).pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.2 this)

variable {E : Type} [Field E] [NumberField E] [Algebra K E] {ι : Type} [Fintype ι] (σ : ι → E →+* ℂ_[l])

end General

section Host

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoBase : D.host.E →+* ℂ_[l] :=
  lam.comp (D.host.φ₀.codRestrict Qbar fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom)

theorem rhoBase_apply (x : D.host.E) : rhoBase D lam x = lamC lam (D.host.φ₀ x) := by
  unfold lamC
  rw [dite_eq_left]
  rfl

def rhoK : D.host.K →+* ℂ_[l] := (rhoBase D lam).comp (algebraMap D.host.K D.host.E)

theorem fst_image_OKp : Prod.fst '' GL3Theta.OKp D lam = (intClosure (rhoK D lam) : Set ℂ_[l]) := by
  let f : 𝓞 D.host.K →+ ℂ_[l] × ℂ_[l] :=
    (((rhoK D lam).prod (((rhoBase D lam).comp (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap D.host.K D.host.E))).comp (algebraMap (𝓞 D.host.K) D.host.K)).toAddMonoidHom
  have hf : (fun a : 𝓞 D.host.K => (GL3Theta.tauK D lam (a : D.host.K), GL3Theta.tauKc D lam (a : D.host.K))) = f := by
    funext a
    exact Prod.ext (rhoBase_apply D lam _).symm (rhoBase_apply D lam _).symm
  unfold GL3Theta.OKp
  rw [hf, image_closure_of_isCompact (isCompact_closure_range (l := l) f) continuous_fst.continuousOn,
    ← Set.range_comp, coe_intClosure]
  rfl

end Host

end GlobalTheory.CompletedBasis
end
end

