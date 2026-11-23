module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeDescentUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def consZero (n : ℕ) : (Fin n → R') →ₗ[R'] (Fin (n + 1) → R') where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp



theorem scalar_descent [IsDomain R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hπ : algebraMap R R' ϖ ≠ 0)
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) :
    ∀ (a : ℕ) (x : R'), (∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ x - x) →
      ∃ c : R, (algebraMap R R' ϖ) ^ a ∣ x - algebraMap R R' c := by
  intro a
  induction a with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ a ih =>
    intro x hx
    obtain ⟨c0, hc0⟩ := hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)
    obtain ⟨t, ht⟩ := hc0
    have hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t := by rw [← ht]; ring
    have ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t := by
      intro σ hσ
      have h := hx σ hσ
      have e : σ x - x = algebraMap R R' ϖ * (σ t - t) := by
        rw [hx']; simp only [map_add (f := _), map_mul, AlgEquiv.commutes]; ring
      rw [e, pow_succ'] at h
      exact (mul_dvd_mul_iff_left hπ).mp h
    obtain ⟨c1, hc1⟩ := ih t ht'
    refine ⟨c0 + ϖ * c1, ?_⟩
    have e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1) := by
      rw [hx']; simp only [map_add (f := _), map_mul]; ring
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hc1

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

theorem main_induction [IsDomain R'] [IsDiscreteValuationRing R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hirr : Irreducible (algebraMap R R' ϖ))
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) (r : ℕ) :
    ∀ (n : ℕ) (N : Submodule R' (Fin n → R')), (∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N) →
      (∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) →
      (∀ v ∈ N, v ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}) ∧
      (∀ u : Fin n → R', (∀ σ ∈ D, (fun i => σ (u i)) - u ∈ N) →
        ∃ a : Fin n → R', (∀ i, a i ∈ Set.range (algebraMap R R')) ∧ u - a ∈ N) := by
  have hπ : algebraMap R R' ϖ ≠ 0 := hirr.ne_zero
  have hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y := by
    rintro σ y ⟨c, rfl⟩; exact AlgEquiv.commutes σ c
  intro n
  induction n with
  | zero =>
    intro N _ _
    refine ⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · have : u - 0 = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    intro N hlat hstab
    set π := algebraMap R R' ϖ with hπdef
    let L := consZero (R' := R') n
    have hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'),
        (fun i => σ (L w i)) = L (fun i => σ (w i)) := by
      intro σ w; funext i
      refine Fin.cases ?_ ?_ i <;> simp [L, consZero]
    let K := N.comap L
    have hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K := fun w => by
      show L (π ^ r • w) ∈ N
      rw [L.map_smul]; exact hlat _
    have hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K := by
      intro σ hσ w hw
      show L _ ∈ N
      rw [← hLact]; exact hstab σ hσ _ hw
    obtain ⟨hPK, hQK⟩ := ih K hKlat hKstab
    let I : Ideal R' := N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)
    have hrI : π ^ r ∈ I := ⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hrI
      exact pow_ne_zero r hπ hrI
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr
    have hmemI : ∀ v ∈ N, π ^ a ∣ v 0 := by
      intro v hv
      have : v 0 ∈ I := ⟨v, hv, rfl⟩
      rw [ha, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by
      have : π ^ a ∈ I := by rw [ha]; exact Ideal.subset_span rfl
      obtain ⟨v, hv, hv0⟩ := this
      exact ⟨v, hv, hv0⟩
    have hpa : π ^ a ∈ Set.range (algebraMap R R') := ⟨ϖ ^ a, by simp [hπdef]⟩

    have hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K := by
      intro σ hσ
      have e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, hvs0, hfix σ _ hpa]
        · intro j; simp [L, consZero, Fin.tail]
      show L _ ∈ N
      rw [e]; exact N.sub_mem (hstab σ hσ _ hvsN) hvsN
    obtain ⟨a0, ha0, ha0K⟩ := hQK (Fin.tail vs) hvsK
    obtain ⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0) := ⟨_, rfl⟩
    have hvoN : vo ∈ N := hvo ▸ N.sub_mem hvsN ha0K
    have hvo0 : vo 0 = π ^ a := by rw [hvo]; simp [L, consZero, hvs0]
    have hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R') := by
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [hvo0]; exact hpa
      · intro j
        have : vo j.succ = a0 j := by rw [hvo]; simp [L, consZero, Fin.tail]
        rw [this]; exact ha0 j
    have hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') →
        x + y ∈ Set.range (algebraMap R R') := by
      rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, map_add _ _ _⟩
    have hrat0 : (0 : R') ∈ Set.range (algebraMap R R') := ⟨0, map_zero _⟩
    have hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) →
        ∀ i, L w i ∈ Set.range (algebraMap R R') := by
      intro w hw i
      refine Fin.cases ?_ ?_ i
      · simpa [L, consZero] using hrat0
      · intro j; simpa [L, consZero] using hw j
    refine ⟨?_, ?_⟩
    ·
      intro v hv
      obtain ⟨t, ht⟩ := hmemI v hv
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo) := ⟨_, rfl⟩
      have hLw : L w = v - t • vo := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, ht, hvo0]; ring
        · intro j; simp [L, consZero, hw, Fin.tail]
      have hwK : w ∈ K := by
        show L w ∈ N
        rw [hLw]; exact N.sub_mem hv (N.smul_mem t hvoN)
      have hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤
          (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L := by
        rw [Submodule.span_le]
        rintro w' ⟨hw'K, hw'r⟩
        exact Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩
      have h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        hspan (hPK w hwK)
      have h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)
      have : v = L w + t • vo := by rw [hLw]; abel
      rw [this]; exact Submodule.add_mem _ h1 h2
    ·
      intro u hu
      have h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0 := by
        intro σ hσ; simpa using hmemI _ (hu σ hσ)
      obtain ⟨c, hc⟩ := scalar_descent D ϖ hπ hres a (u 0) h0
      obtain ⟨t, ht⟩ := hc
      obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0 := ⟨_, rfl⟩
      have herat : ∀ i, e i ∈ Set.range (algebraMap R R') := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [he]; exact ⟨c, rfl⟩
        · intro j; rw [he]; simpa using hrat0
      obtain ⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail u' := ⟨_, rfl⟩
      have hLw : L w = u' := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, consZero, hu', he, hvo0]; rw [ht, hπdef]; ring
        · intro j; simp [L, consZero, hw, Fin.tail]
      have hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K := by
        intro σ hσ
        have key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo := by
          rw [L.map_sub, ← hLact, hLw, hu']
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
            hfix σ _ (herat i), hfix σ _ (hvorat i)]
          ring
        show L _ ∈ N
        rw [key]; exact N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)
      obtain ⟨a', ha', ha'K⟩ := hQK w hwinv
      refine ⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩
      have : u - (e + L a') = t • vo + L (w - a') := by
        rw [L.map_sub, hLw, hu']; abel
      rw [this]; exact N.add_mem (N.smul_mem t hvoN) ha'K

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

theorem stable_lattice_descent_unramified (R R' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (D : Set (R' ≃ₐ[R] R'))
    (hres : ∀ x : R', (∀ σ ∈ D, σ x - x ∈ maximalIdeal R') →
      ∃ r : R, x - algebraMap R R' r ∈ maximalIdeal R')
    (n r : ℕ) (N : Submodule R' (Fin n → R'))
    (hlat : (maximalIdeal R') ^ r • (⊤ : Submodule R' (Fin n → R')) ≤ N)
    (hstab : ∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) :
    N = Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c := by
    intro x hx
    obtain ⟨c, hc⟩ := hres x fun σ hσ => by
      rw [hmax, Ideal.mem_span_singleton]; exact hx σ hσ
    rw [hmax, Ideal.mem_span_singleton] at hc
    exact ⟨c, hc⟩
  have hmem : algebraMap R R' ϖ ∈ maximalIdeal R' := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N := fun w =>
    hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)
  obtain ⟨hP, -⟩ :=
    StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab
  exact le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableRationalSchwartzBruhatMulPolynomialDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LatSumSB

open GlobalTheory.WeilM GlobalTheory.ThetaTrCont

theorem summable_sb_mul_decay : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∀ (a : κ → FiniteAdeleRing (𝓞 F) F), ∃ M : ℕ, ∀ c : κ → mixedEmbedding.mixedSpace F,
      Summable fun ξ : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + a i)‖ *
        ((1 + ‖((fun i => mixedEmbedding F (ξ i)) + c : κ → mixedEmbedding.mixedSpace F)‖) ^ M)⁻¹ := by
  intro F _ _ κ _ g hg a
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hK : IsCompact ((fun z => z - a) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := exists_nat_mul_integral_of_isCompact F hK
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, fun c => ?_⟩
  set M := Module.finrank ℤ (denomLattice F κ N) + 1
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_left ?_ _
    rw [norm_eq_zero]
    by_contra h0
    apply hξ
    have hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ (fun z => z - a) '' tsupport g :=
      ⟨_, subset_tsupport _ h0, by funext i; simp⟩
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy'⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hKN _ hy i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy'
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded
      ((((summable_one_add_norm_inv (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj).mul_left
        ((1 + ‖c‖) ^ M)).mul_left B) fun ξ => ?_
    set z : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ.1 i)
    have hz : ‖(j ξ : denomLattice F κ N)‖ = ‖z‖ := rfl
    simp only [Function.comp_apply, hz]
    have hpos1 : 0 < (1 + ‖z + c‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hpos2 : 0 < (1 + ‖z‖) ^ M := pow_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)) M
    have hw : ((1 + ‖z + c‖) ^ M)⁻¹ ≤ (1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos2, ← div_eq_inv_mul, div_le_iff₀ hpos1, ← mul_pow, mul_comm (1 + ‖c‖)]
      exact pow_le_pow_left₀ (add_pos_of_pos_of_nonneg one_pos (norm_nonneg _)).le (one_add_norm_le z c) M
    rw [norm_mul, norm_norm, Real.norm_of_nonneg (inv_nonneg.2 hpos1.le)]
    calc ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i) + a i)‖ * ((1 + ‖z + c‖) ^ M)⁻¹
        ≤ B * ((1 + ‖c‖) ^ M * ((1 + ‖z‖) ^ M)⁻¹) :=
          mul_le_mul (hB _) hw (inv_nonneg.2 hpos1.le) ((norm_nonneg _).trans (hB 0))
      _ = _ := rfl

end GlobalTheory.LatSumSB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartLeft
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEv.PartLTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def reindexFun {R : Type} {ι ι' : Type} (e : ι ≃ ι') : ((ι → R) → ℂ) →ₗ[ℂ] ((ι' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun y : ι' → R => y ∘ e)

theorem reindexFun_apply {R : Type} {ι ι' : Type} (e : ι ≃ ι') (Φ : (ι → R) → ℂ) (y : ι' → R) :
    reindexFun e Φ y = Φ (y ∘ e) := rfl

theorem isTame_reindexFun {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    IsTame F (reindexFun (R := AF F) e) := by
  intro g hg
  let L : (ι' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (ι → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e).toContinuousLinearEquiv
  let H : (ι' → FiniteAdeleRing (𝓞 F) F) ≃ₜ (ι → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun y => y ∘ e
      invFun := fun z => z ∘ e.symm
      left_inv := fun y => by funext i; simp
      right_inv := fun z => by funext i; simp
      continuous_toFun := continuous_pi fun i => continuous_apply (e i)
      continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i) }
  refine ⟨Unit, inferInstance, fun _ => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun _ => g ∘ H,
    fun _ => ⟨hg.1.comp_continuous H.continuous, hg.2.comp_homeomorph H⟩, fun f => ?_⟩
  funext y
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem isTame_partL : ∀ (F : Type) [Field F] [NumberField F] (κ κ₁ κ' : Type) [Fintype κ] [Fintype κ₁] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)), IsTame F T → IsTame F (partL (κ' := κ') T) := by
  intro F _ _ κ κ₁ κ' _ _ _ T hT
  have h : partL (κ' := κ') T = reindexFun (Equiv.sumComm κ' κ₁) ∘ₗ partR (κ := κ') T ∘ₗ
      reindexFun (Equiv.sumComm κ κ') := by
    refine LinearMap.ext fun Φ => funext fun s => ?_
    simp only [LinearMap.comp_apply, reindexFun_apply, partR_apply, partL_apply]
    exact congrArg₂ (fun φ t => T φ t) (funext fun x => congrArg Φ (funext fun i => by cases i <;> rfl)) rfl
  rw [h]
  exact ((isTame_reindexFun _).comp (GlobalTheory.T.tame_part_right F κ' κ κ₁ T hT)).comp (isTame_reindexFun _)

end GlobalTheory.DoublingEv.PartLTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

theorem tate_lev_surj : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  intro l _ M _ hroot n x hx
  choose r hr using hroot
  have key : ∀ (m : ℕ) (y : M), (r^[m] y) ^ l ^ m = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, hr]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun m => (r^[m] x) ^ l ^ n) fun m => ⟨?_, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, key, hx]
  · rw [← pow_mul, mul_comm, pow_mul, Function.iterate_succ_apply', hr]
  · rw [GlobalTheory.HTLat.Tate.lev_mk, key]

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefiniteStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_standard_character_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  first | exact @GlobalTheory.WeilContF.continuous_of_level_real | exact GlobalTheory.WeilContF.continuous_of_level_real | (intros; apply GlobalTheory.WeilContF.continuous_of_level_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof

theorem exists_prime_natCast_ne_zero (k : Type) [Field k] :
    ∃ (l : ℕ) (_ : Fact l.Prime), (l : k) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : k) = 0
  · refine ⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩
    have : ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1 := by push_cast; ring
    rw [← this, h2, h3, sub_zero]
  · exact ⟨2, ⟨Nat.prime_two⟩, h2⟩

theorem torsionUnramified_imp_tate_and_infinite :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω]
      [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
      (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) →
      (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ V A _ _ hb
  obtain ⟨l, hl, hl0⟩ := exists_prime_natCast_ne_zero (ResidueField R)
  have hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0 := fun n => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hl0
  refine ⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩

end GlobalTheory.Proof
end

