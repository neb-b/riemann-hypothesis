module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormsCentralTranslateIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.CentralTranslate

open GlobalTheory.FreeBlockTwist Matrix
open GlobalTheory.StdFrames (cpt)

variable {D : D7} {S T : HSp D}

theorem exists_pow_latAt {B : Base S T} (hF : B.F.Good) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ}
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h : Bridge.Gf S, ∀ x ∈ B.latAt h,
      ((N ^ l : ℕ) : 𝓞 D.host.E) • x ∈ B.latAt (h * (finPt S k)⁻¹) := by
  classical
  have hβ := hF.frS
  choose m hm using fun ij : Fin S.rank × Fin S.rank =>
    GlobalTheory.StdFrames.exists_pow_mul_mem (N := N)
      (((B.F.βS⁻¹).1 * (Formalism.L2.Theta.mt S k).map (toEAf D) * B.F.βS.1) ij.1 ij.2) fun PP hPP =>
      conj_entry (toEAf D) B.F.βS hk (cpt PP) (ha PP hPP) (PP.adicCompletionIntegers D.host.E) (zero_mem _) (one_mem _) ij.1 ij.2
  refine ⟨Finset.univ.sup m, fun l hl h x hx => ?_⟩
  have hx' : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => eToEAf D (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS := hx
  have h3 := (hβ _).1 hx'
  have h4 := (hβ _).2 (conj_mulVec _ B.F.βS _ (fun i j => hm (i, j) l ((Finset.le_sup (Finset.mem_univ _)).trans hl)) h3)
  change ((Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹).1 *ᵥ (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) ∈
    Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS
  have e1 : (Formalism.UG.bc (Lev.swapAE D) (h * (finPt S k)⁻¹).1)⁻¹ =
      Formalism.UG.bc (Lev.swapAE D) (finPt S k).1 * (Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv, _root_.mul_inv_rev, inv_inv]
  have e2 : (fun i => eToEAf D ((((N ^ l : ℕ) : 𝓞 D.host.E) • x) i)) = (N ^ l) • fun i => eToEAf D (x i) := by
    funext i
    rw [Nat.cast_smul_eq_nsmul, Pi.smul_apply, Pi.smul_apply, map_nsmul]
  rw [e1, e2, Units.val_mul, mulVec_nsmul]
  convert h4 using 1
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul]
  rfl

theorem coefLatFn_le {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ)
    {n : ℕ} (lam : D.what₂.Tau → DomWeight n) {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O) (hM : Submodule.IsFullLattice D.host.E M) (h1 : ∀ x ∈ M, (N : 𝓞 D.host.E) • x ∈ M')
    (h2 : ∀ x ∈ M', (N : 𝓞 D.host.E) • x ∈ M) : coefLatFn σ emb O lam M ≤ coefLatFn σ emb O lam M' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  have h3 : coefFn σ lam (((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F : VV K lam) : Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O lam M' :=
    Submodule.subset_span ⟨_, nabAtr_scale emb lam N (by first | exact hM.toIsLattice | exact hM) h1 h2 F hF, rfl⟩
  have h4 := Submodule.smul_mem _ ((⟨_, hO⟩ : O) ^ GlobalTheory.NabScale.scaleExp lam) h3
  have h0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [SetLike.mem_coe]
  convert h4 using 1
  funext x
  change _ = ((N : ℂ)⁻¹) ^ GlobalTheory.NabScale.scaleExp lam * coefFn σ lam ((N : K) ^ GlobalTheory.NabScale.scaleExp lam • F.1) x
  rw [coefFn, coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_pow, map_natCast, inv_pow]
  field_simp

theorem coefLat_mul {B : Base S T} (hF : B.F.Good) {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) {a : AE D} {k : GA D S} (hk : SuppAt a S k) {N : ℕ} (hN : N ≠ 0)
    (hO : (N : ℂ)⁻¹ ∈ O)
    (ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (a + cA D a)) = 0) (h : Bridge.Gf S) :
    B.coefLat σ emb O (h * finPt S k) = B.coefLat σ emb O h := by
  obtain ⟨m₁, h₁⟩ := exists_pow_latAt hF hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_latAt hF (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  have e1 := h₁ (m₁ + m₂) (Nat.le_add_right _ _) (h * finPt S k)
  have e2 := h₂ (m₁ + m₂) (Nat.le_add_left _ _) h
  rw [mul_inv_cancel_right] at e1
  rw [show finPt S k⁻¹ = (finPt S k)⁻¹ from MonoidHom.map_inv _ k, inv_inv] at e2
  have hL : ∀ y : Bridge.Gf S, Submodule.IsFullLattice D.host.E (B.latAt y) := by
    intro y
    classical
    have hspan : Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E)) = ⊤ := by
      let W := Submodule.span D.host.E (B.F.ΛS : Set (Fin S.rank → D.host.E))
      change W = ⊤
      by_contra hW
      let g : (Fin S.rank → D.host.E) →ₗ[D.host.E] Module.Dual D.host.E W :=
        { toFun := fun x => { toFun := fun y => ∑ i, ∑ j, x i * S.gram i j * y.1 j
                              map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
                              map_smul' := by intros; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
          map_add' := by intros; ext y; simp [add_mul, Finset.sum_add_distrib]
          map_smul' := by intros; ext y; simp [mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum] }
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (Fin S.rank → D.host.E) := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt hW
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      let v : Fin S.rank → D.host.E := fun i => star (x i)
      have hv0 : v ≠ 0 := by
        intro hv
        apply hx0
        funext i
        have hi := congrFun hv i
        simpa [v] using congrArg star hi
      have hline (r : D.host.E) : r • v ∈ B.F.ΛS := by
        apply (hF.sdS.2 _).2
        intro y hy
        have hz : (∑ i, ∑ j, x i * S.gram i j * y j) = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hzy : (∑ i, ∑ j, star (y i) * S.gram i j * v j) = 0 := by
          have hg (i j : Fin S.rank) : star (S.gram i j) = S.gram j i := by
            exact S.herm.eq _ _
          have hs : (starRingEnd D.host.E) (∑ i, ∑ j, x i * S.gram i j * y j) = 0 := by rw [hz, map_zero]
          simp only [map_sum, map_mul] at hs
          change (∑ i, ∑ j, star (x i) * star (S.gram i j) * star (y j)) = 0 at hs
          simp only [hg] at hs
          rw [Finset.sum_comm] at hs
          simpa [mul_comm, mul_left_comm, mul_assoc] using hs
        refine ⟨0, ?_⟩
        simp only [map_zero, Pi.smul_apply, smul_eq_mul]
        calc
          0 = r * (∑ i, ∑ j, star (y i) * S.gram i j * v j) := by rw [hzy, mul_zero]
          _ = ∑ i, ∑ j, star (y i) * S.gram i j * (r * v j) := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hn
        apply hv0
        funext i
        simpa using not_exists.mp hn i
      let coord := (LinearMap.proj i : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E).restrictScalars (𝓞 D.host.E)
      have htop : B.F.ΛS.map coord = ⊤ := by
        rw [eq_top_iff]
        intro a _
        exact ⟨(a / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 D.host.E) D.host.E := Module.finite_def.mpr (htop ▸ hF.sdS.1.fg.map coord)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    exact Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hspan _
  have hO' : ((N ^ (m₁ + m₂) : ℕ) : ℂ)⁻¹ ∈ O := by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem hO _
  have e := le_antisymm (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e1 e2)
    (coefLatFn_le σ emb O B.w.lam (pow_ne_zero _ hN) hO' (hL _) e2 e1)
  unfold Base.coefLat harmLat
  rw [e]

theorem translate_mem_formsC {B : Base S T} {ψ : Twist D Circle} {c : Bridge.Gf S} (hc : ∀ g, g * c = c * g)
    {f : Bridge.Gf S → PolF D T.rank S.rank} (hf : f ∈ B.formsC ψ) : (fun h => f (h * c)) ∈ B.formsC ψ := by
  rw [Base.mem_formsC] at hf ⊢
  refine ⟨fun h => hf.1 _, fun γ h k => ?_⟩
  have := hf.2 γ (h * c) k
  rw [← mul_assoc, mul_assoc _ c, ← hc, ← mul_assoc] at this
  exact this

theorem mem_mtLat_iff_translate : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ (ψ : Twist D Circle) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O →
  ∀ (Q : Finset (Pl D.host.E)) (z : GA D (Vc D j)), IsCentAt j Q z → ∀ N : ℕ, N ≠ 0 → (∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ P.asIdeal) → (N : ℂ)⁻¹ ∈ O →
  ∀ F : Amb D j, F ∈ B.mtLat σ emb O ψ ↔ (fun h => F (h * finPt (Vc D j) z)) ∈ B.mtLat σ emb O ψ := by
  intro D j B hB ψ K _ _ σ emb O _ Q z hz N hN hQ hO F
  obtain ⟨hzc, -, e, he, hsupp⟩ := hz
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal → cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  have hc : ∀ g : Bridge.Gf (Vc D j), g * finPt (Vc D j) z = finPt (Vc D j) z * g := fun g => by
    obtain ⟨y, rfl⟩ := (finHom (Vc D j)).rangeRestrict_surjective g
    rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, Subgroup.mem_center_iff.1 hzc y]
  have hc' : ∀ g : Bridge.Gf (Vc D j), g * (finPt (Vc D j) z)⁻¹ = (finPt (Vc D j) z)⁻¹ * g := fun g =>
    (Commute.inv_right (hc g)).eq
  have hl := coefLat_mul hB.frame σ emb O hsupp hN hO ha
  rw [Base.mem_mtLat, Base.mem_mtLat]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨translate_mem_formsC hc h1, fun h => hl h ▸ h2 _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => ?_⟩
    · have := translate_mem_formsC hc' h1
      simp only [inv_mul_cancel_right] at this
      exact this
    · have := h2 (h * (finPt (Vc D j) z)⁻¹)
      rw [← hl] at this
      simp only [inv_mul_cancel_right] at this
      exact this

end GlobalTheory.CentralTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralIffSelfDualTraceCharacterSplitPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ScalarSelfDual

theorem eq_of_parts {D : D7} {x y : AE D} (hx : infPart D x = 0) (hy : infPart D y = 0)
    (h : toEAf D x = toEAf D y) : x = y := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_sub, hx, hy, sub_zero]) ?_
  rw [map_sub, sub_eq_zero]
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem mul_hO_of_half {D : D7} {S T : HSp D} {e : AE D} {l : WO S T} (hl : IsHalf e l) (u : WO S T) :
    e * hO S T l u = hO S T l u := by
  unfold hO
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [mul_left_comm, hl d a]


set_option maxHeartbeats 800000 in
theorem exists_half_frMapO {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (hee : e * e = e) (z : Matrix (Fin T.rank) (Fin S.rank) (EAf D))
    (hz : ∀ i j, toEAf D e * z i j = z i j) :
    ∃ y : WO S T, IsHalf e y ∧ frMapO S T βS βT y = z := by
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (HMul.hMul βT.val z) (βS⁻¹).val
  refine ⟨Matrix.of fun i j => e * L (N i j), fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, hee]
  · have hY : ((Matrix.of fun i j => e * L (N i j) : WO S T).map (toEAf D)) = toEAf D e • N := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, map_mul, hL, Matrix.smul_apply, smul_eq_mul]
    have h1 : HMul.hMul (βT⁻¹).val βT.val = (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D)) := Units.inv_mul βT
    have h2 : HMul.hMul (βS⁻¹).val βS.val = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) := Units.inv_mul βS
    have e1 : HMul.hMul (HMul.hMul (βT⁻¹).val N) βS.val = z := by
      simp only [N, Matrix.mul_assoc]
      rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    unfold frMapO
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, e1]
    exact Matrix.ext fun i j => hz i j

theorem frMapO_half {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} {l : WO S T} (hl : IsHalf e l) (i : Fin T.rank) (j : Fin S.rank) :
    toEAf D e * frMapO S T βS βT l i j = frMapO S T βS βT l i j := by
  have hY : toEAf D e • (l.map (toEAf D)) = l.map (toEAf D) := by
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, hl i j]
  have : toEAf D e • frMapO S T βS βT l = frMapO S T βS βT l := by
    unfold frMapO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hY]
  exact congrFun (congrFun this i) j

theorem trace_single_mul' {R : Type} [CommRing R] {m n : ℕ} (i : Fin m) (j : Fin n) (a : R)
    (M : Matrix (Fin n) (Fin m) R) : Matrix.trace (Matrix.single i j a * M) = a * M j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]


set_option maxHeartbeats 1600000 in
theorem int_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → 0 < S.rank → 0 < T.rank → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ Z : AE D, e * Z = Z → (toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ Z' : AE D, e * Z' = Z' → toEAf D Z' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z'))) = 1) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hfS hfT hs ht Q e he hQ Z hZ
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hfin : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hsupp : ∀ x : AE D, e * x = x → infPart D x = 0 := fun x hx => by
    rw [← hx, map_mul, hinf, zero_mul]
  let i₀ : Fin S.rank := ⟨0, hs⟩
  let j₀ : Fin T.rank := ⟨0, ht⟩
  have hsingle : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : AE D), e * x = x → ∀ a b,
      toEAf D e * Matrix.single i j (toEAf D x) a b = Matrix.single i j (toEAf D x) a b := by
    intro m n i j x hx a b
    simp only [Matrix.single_apply]
    split_ifs
    · rw [← map_mul, hx]
    · rw [mul_zero]
  have hint : ∀ {m n : ℕ} (i : Fin m) (j : Fin n) (x : EAf D),
      IsIntM (Matrix.single i j x) ↔ x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro m n i j x
    constructor
    · intro h
      have := h i j
      rwa [Matrix.single_apply_same] at this
    · intro h a b
      simp only [Matrix.single_apply]
      split_ifs
      · exact h
      · exact zero_mem _
  obtain ⟨u, hu, -, huZ⟩ := _root_.GlobalTheory.AdjHalfLift.exists_half_frMapAdj D S T βS βT e hee (Matrix.single i₀ j₀ (toEAf D Z)) (hsingle i₀ j₀ Z hZ)
  have hval : ∀ (l : WO S T) (Z' : AE D), IsHalf e l → e * Z' = Z' → toEAf D Z' = frMapO S T βS βT l j₀ i₀ →
      symplO S T l u = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (Z * Z')) := by
    intro l Z' hl hZ' h
    have : hO S T l u = Z * Z' := by
      refine eq_of_parts (hsupp _ (mul_hO_of_half hl u)) (by rw [map_mul, hsupp Z hZ, zero_mul]) ?_
      rw [GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT u l, huZ, trace_single_mul', map_mul, h]
    unfold symplO
    rw [this]
  have h1 : toEAf D Z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ u ∈ latO S T ΛS ΛT (fun _ => True) := by
    rw [← hint i₀ j₀, ← huZ]
    exact ⟨GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u hu,
      fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ u h hu⟩
  rw [h1, _root_.GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf D ψ S T ΛS ΛT hψ hS hT e hee he.2 hinf hfin u hu]
  constructor
  · intro h Z' hZ' hZi
    obtain ⟨l, hl, hlZ⟩ := exists_half_frMapO S T βS βT hee (Matrix.single j₀ i₀ (toEAf D Z')) (hsingle j₀ i₀ Z' hZ')
    rw [← hval l Z' hl hZ' (by rw [hlZ, Matrix.single_apply_same])]
    refine h l ((_root_.GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).2 ?_) hl
    rw [hlZ, hint]
    exact hZi
  · intro h l hlm hl
    have hI := (_root_.GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT hfS hfT Q e he hQ l hl).1 hlm
    obtain ⟨Y, -, hY⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) (frMapO S T βS βT l j₀ i₀)
    have hZ' : e * (e * Y) = e * Y := by rw [← mul_assoc, hee]
    have hE : toEAf D (e * Y) = frMapO S T βS βT l j₀ i₀ := by
      rw [map_mul, hY, frMapO_half βS βT hl]
    rw [hval l (e * Y) hl hZ' hE]
    exact h _ hZ' (by rw [hE]; exact hI j₀ i₀)

end GlobalTheory.ScalarSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterOfLocalLanglands
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.GalLoc.PsiLvl

def PsiRead (D : D7) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) : Prop :=
  ∀ (i : D.ntw.Tw) (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
    ((D.nexp.psiU i true ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)
        (D.ntw.emb0 i ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0))

theorem exists_theta_of_eq {D₀ : D7} {L : LocAll (lay0 D₀)} {D' : D7} (h : D' = withLoc L)
    (θ0 : ∀ kk : Fin 2, Multiplicative (ZMod ((withLoc L).host.g kk)) →* (↥(withLoc L).LL0)ˣ)
    (h0 : PsiRead (withLoc L) θ0) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ, HEq θ θ0 ∧ PsiRead D' θ := by
  subst h
  exact ⟨θ0, HEq.rfl, h0⟩

end GlobalTheory.GalLoc.PsiLvl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentComplexOfSubfieldCoeffLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceIndep

theorem sum_dual_smul_eq_zero {W ι I : Type} [AddCommGroup W] [Module ℂ W] (F : Subfield ℂ) {b : ι → W}
    (hb : LinearIndependent ℂ b) {v : I → W} (hv : ∀ a, v a ∈ Submodule.span F (Set.range b)) (s : Finset I) (c : I → ℂ)
    (h : ∑ a ∈ s, c a • v a = 0) (φ : Module.Dual F ℂ) : ∑ a ∈ s, φ (c a) • v a = 0 := by
  classical
  choose g hg using fun a => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv a)
  set t := s.biUnion fun a => (g a).support with ht
  have hv' : ∀ a ∈ s, v a = ∑ k ∈ t, g a k • b k := fun a ha => by
    rw [← hg a]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun a => (g a).support) ha) _ fun _ _ => zero_smul _ _
  have h1 : ∑ k ∈ t, (∑ a ∈ s, g a k • c a) • b k = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv' a ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_assoc, smul_comm]
  have h2 := linearIndependent_iff'.1 hb t _ h1
  rw [Finset.sum_congr rfl fun a ha => by rw [hv' a ha, Finset.smul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have h3 := congrArg φ (h2 k hk)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h3
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, Finset.sum_congr rfl fun a _ => by rw [mul_comm, ← smul_eq_mul, ← map_smul], h3, zero_smul]

theorem coefLatFn_mem_span {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {F : Subfield ℂ} (hF : O ≤ F.toSubring)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {φ : GLR D n → ℂ}
    (h : φ ∈ coefLatFn σ emb O lam M) :
    φ ∈ Submodule.span F (Set.range fun k => HarmLattice.cf lam (GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k))) := by
  have hσ : ∀ x : K, σ x ∈ F := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    exact div_mem (hF (hc.int a)) (hF (hc.int b))
  induction h using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨G, -, rfl⟩ := h
    rw [HarmLattice.coefFn_eq]
    have hG : G ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hG using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a G _ h1 =>
      rw [LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hσ a⟩ : F) h1
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c.1, hF c.2⟩ : F) h1

theorem linearIndependent_complex : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  intro D S T B hB K _ _ σ emb O hc F hF I f hf hli
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hcf : Function.Injective (HarmLattice.cf B.w.lam) :=
    (injective_iff_map_eq_zero _).2 fun G hG => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D _ B.w.lam G fun x => congrFun hG x)
  have hb := (GlobalTheory.CoefModel.linearIndependent_mapVV σ B.w.lam).map' (HarmLattice.cf B.w.lam) (LinearMap.ker_eq_bot.2 hcf)
  refine linearIndependent_iff'.2 fun s c h a ha => (Module.forall_dual_apply_eq_zero_iff F (c a)).1 fun φ => ?_
  refine linearIndependent_iff'.1 hli s (fun a => φ (c a)) (funext fun y => ?_) a ha
  refine _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ B.w B.F.BS hB.wt hpq _ ?_ ?_
  · rw [Finset.sum_apply]
    exact sum_mem fun a _ => Submodule.smul_mem _ (φ (c a) : ℂ) (hf a y).1
  · have h0 := congrArg (harmFn T.rank B.w B.F.BS) (congrFun h y)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at h0
    simp only [Pi.smul_apply, map_smul] at h0
    have := sum_dual_smul_eq_zero F hb (fun a => coefLatFn_mem_span hc hF B.w.lam _ (hf a y).2) s c h0 φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun a _ => (harmFn T.rank B.w B.F.BS).map_smul (φ (c a) : ℂ) (f a y)

end GlobalTheory.PlaceIndep

end
end

