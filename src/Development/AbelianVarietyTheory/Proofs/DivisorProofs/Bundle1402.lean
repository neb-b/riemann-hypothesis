module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxTransfersHaarFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatDarbouxTransfer

theorem finrank_AE (D : D7) : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) ∧
    Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin, D.sp.cm.deg2]⟩

theorem finrank_pair (K : Type) [Field K] (κ : Type) [Fintype κ] :
    Module.finrank K ((κ → K) × (κ → K)) = 2 * Fintype.card κ := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  ring

theorem finrank_mat (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (m n : ℕ) :
    Module.finrank K (Matrix (Fin m) (Fin n) L) = m * n * Module.finrank K L := by
  show Module.finrank K (Fin m → Fin n → L) = _
  simp [Module.finrank_pi_fintype, mul_assoc]

theorem card_eq (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) :
    Fintype.card κ = T.rank * S.rank := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have h := e.finrank_eq
  have ha : Module.finrank (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) = T.rank * S.rank * 2 := by
    show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AE D) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  have : T.rank * S.rank * 2 = 2 * Fintype.card κ := ha.symm.trans (h.trans hb)
  omega

set_option maxHeartbeats 1000000 in
theorem onto (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, e.symm p ∈ ratL T S := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have hκ := card_eq D S T κ e
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
    LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
  let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) := J1.prodMap J1
  let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars D.host.F).comp I
  haveI : Nontrivial (AE D) := Module.nontrivial_of_finrank_pos (R := AF D.host.F) (by rw [hAE]; norm_num)
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    refine (finrank_mat D.host.F D.host.E T.rank S.rank).trans ((finrank_pair D.host.F κ).trans ?_).symm
    rw [hκ, D.sp.cm.deg2]
    ring
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM D.host.F x) = J (y, z) := hx
  show incM D.host.F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

end GlobalTheory.RatDarbouxTransfer

namespace GlobalTheory.RatDarbouxTransfer

open scoped Pointwise


set_option maxHeartbeats 1000000 in
theorem haar_fundDomain_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro D ψ _ S T JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  haveI hMT : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  let ce : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃L[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : Formalism.IndefR.Datum.WO S T ≃ₜ+ (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : Formalism.IndefR.Datum.WO S T ≃ᵐ (κ → AF D.host.F) × (κ → AF D.host.F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratL T S, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, co.e.symm p ∈ ratL T S :=
    onto D S T κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : Formalism.IndefR.Datum.WO S T) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratL T S := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratL T S := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratL T S => co.e (t : Formalism.IndefR.Datum.WO S T)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) (k : ratL T S),
          (k : Formalism.IndefR.Datum.WO S T) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF D.host.F) × (κ → AF D.host.F)) + co.e w = co.e ((k : Formalism.IndefR.Datum.WO S T) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealTraceArchimedeanEmbeddingsNondegenerate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfTraceNondeg

variable {K : Type} [Field K] [NumberField K]

theorem norm_algebraMap_apply (x : K) (v : InfinitePlace K) :
    ‖(algebraMap K (InfiniteAdeleRing K) x) v‖ = v x := by
  simp [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe, InfinitePlace.coe_apply]

theorem norm_eq_of_cont (χ : InfiniteAdeleRing K →+* ℂ) (hχ : Continuous χ) (φ : K →+* ℂ)
    (h : ∀ x, χ (algebraMap K _ x) = φ x) (a : InfiniteAdeleRing K) :
    ‖χ a‖ = ‖a (InfinitePlace.mk φ)‖ := by
  have hc1 : Continuous fun a => ‖χ a‖ := hχ.norm
  have hc2 : Continuous fun a : InfiniteAdeleRing K => ‖a (InfinitePlace.mk φ)‖ :=
    (continuous_apply (InfinitePlace.mk φ)).norm
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap K).equalizer hc1 hc2 (funext fun x => ?_)) a
  simp only [Function.comp, h, norm_algebraMap_apply, InfinitePlace.apply]

end GlobalTheory.InfTraceNondeg

namespace GlobalTheory.InfTraceNondeg


set_option synthInstance.maxHeartbeats 400000 in
theorem realTrace_nondeg : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → ∀ a : Ainf D.host.F, a ≠ 0 →
      ∃ b : Ainf D.host.F, (∑ ρ, θ ρ ((a * b) ⊗ₜ[D.host.F] (1 : D.host.E))).re ≠ 0 := by
  intro D θ hθ a ha
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := D.host.F) (K := D.host.E) v
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 w
  let χ : D.what₂.Tau → (Ainf D.host.F →+* ℂ) := fun σ =>
    (θ σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hχapp : ∀ σ c, χ σ c = θ σ (c ⊗ₜ[D.host.F] (1 : D.host.E)) := fun _ _ => rfl
  have hχalg : ∀ σ (x : D.host.F), χ σ (algebraMap D.host.F (Ainf D.host.F) x) =
      ((tauE D σ).comp (algebraMap D.host.F D.host.E)) x := by
    intro σ x
    rw [hχapp, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', (hθ σ).1]
    rfl
  have hnorm : ∀ σ c, ‖χ σ c‖ = ‖c (InfinitePlace.mk ((tauE D σ).comp (algebraMap D.host.F D.host.E)))‖ :=
    fun σ c => norm_eq_of_cont (χ σ) (hθ σ).2 _ (hχalg σ) c
  have hmul : ∀ x y : Ainf D.host.F, ∀ u, (x * y) u = x u * y u := fun _ _ _ => rfl
  set e : Ainf D.host.F := Pi.single v 1 with he
  set b : Ainf D.host.F := Pi.single v (a v)⁻¹ with hb
  have hab : a * b = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu
      simp [he, hb, hv]
    · simp [he, hb, Pi.single_apply, hu]
  have hee : e * e = e := by
    funext u
    rw [hmul]
    by_cases hu : u = v
    · subst hu; simp [he]
    · simp [he, Pi.single_apply, hu]
  have hidem : ∀ σ, χ σ e = 0 ∨ χ σ e = 1 := by
    intro σ
    have h1 : χ σ e * χ σ e = χ σ e := by rw [← map_mul, hee]
    have h2 : χ σ e * (χ σ e - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hplace : InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E)) = v := by
    rw [← InfinitePlace.comap_mk]
    change (InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ)).comap _ = v
    have hρ' : InfinitePlace.mk (Formalism.MainNotions.StandardLattice.embOf D ρ) = w := hρ
    have hw' : w.comap (algebraMap D.host.F D.host.E) = v := hw
    rw [hρ', hw']
  have hρ1 : χ ρ e = 1 := by
    rcases hidem ρ with h | h
    · exfalso
      have := hnorm ρ e
      rw [h, hplace, he, Pi.single_eq_same, norm_zero, norm_one] at this
      exact zero_ne_one this
    · exact h
  refine ⟨b, ?_⟩
  rw [hab, Complex.re_sum]
  have hterm : ∀ σ, 0 ≤ (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re := by
    intro σ
    rw [← hχapp]
    rcases hidem σ with h | h <;> simp [h]
  have hge : (θ ρ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re ≤ ∑ σ, (θ σ (e ⊗ₜ[D.host.F] (1 : D.host.E))).re :=
    Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ ρ)
  rw [← hχapp, hρ1, Complex.one_re] at hge
  linarith

end GlobalTheory.InfTraceNondeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTargetF

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dblG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin (n + n)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl J)

theorem isHermND_dblG {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) :
    IsHermND σ (dblG J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;>
      simp [dbl, h.1 i j]
  · rw [dblG, Matrix.det_reindex_self, dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp [h.2]

theorem reindex_dbl_incM {n : ℕ} {J JA : Matrix (Fin n) (Fin n) E} (hA : JA = Jᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl (incM F JA)) = incM F (dblG J)ᵀ := by
  subst hA
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [dblG, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.map_apply] <;> simp [dbl]

abbrev coDbl {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) :
    Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) (κ ⊕ κ) :=
  reindexRows finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA)

theorem coDbl_rat {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ ⊕ κ → F,
      (coDbl hA co).e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro x
  obtain ⟨y₁, z₁, h₁⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inl) id)
  obtain ⟨y₂, z₂, h₂⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inr) id)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e₁ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inl id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
  have e₂ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inr id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
  rw [coDbl, reindexRows_e, dblRows_e, e₁, e₂, h₁, h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;> simp

theorem isHeckeCharF_one : Formalism.IndefR.DatumF.IsHeckeCharF (1 : (AF F ⊗[F] E)ˣ →* Circle) :=
  ⟨continuous_const, fun _ => rfl⟩

theorem resEtaF_one_dbl (h2 : Module.finrank F E = 2) {χ : (AF F ⊗[F] E)ˣ →* Circle} {n : ℕ}
    (hr : Formalism.IndefR.DatumF.ResEtaF χ n) : Formalism.IndefR.DatumF.ResEtaF (1 : (AF F ⊗[F] E)ˣ →* Circle) (n + n) :=
  ⟨hr.1, fun η hη a => by
    have h4 := hη.2.2.1 (Formalism.IndefR.DatumF.idFF F E a)
    have h5 : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Formalism.IndefR.DatumF.idFF F E a) = a ^ 2 :=
      Units.ext (by
        change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) a.1) = _
        have : Nontrivial (AF F) :=
          (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
        rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = η a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def ugDbl {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ) :
    UG (cA σ) (dbl (incM F JA)) →* UG (cA σ) (incM F (dblG JT)ᵀ) :=
  ugReindex finSumFinEquiv (reindex_dbl_incM hA)

theorem ugDbl_coe {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ)
    (g : UG (cA σ) (dbl (incM F JA))) :
    (ugDbl hA g).1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv g.1.1 := rfl

end GlobalTheory.WeilSchrodinger.DblTargetF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOfCompEqId
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.TangentStalk

theorem ker_eq_maximalIdeal {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g : R →+* k) (hg : g.comp j = RingHom.id k) : RingHom.ker g = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g
    (fun c => ⟨j c, RingHom.congr_fun hg c⟩))

theorem ringHom_eq_of_comp_eq_id {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g₁ g₂ : R →+* k) (h₁ : g₁.comp j = RingHom.id k) (h₂ : g₂.comp j = RingHom.id k) : g₁ = g₂ := by
  ext a
  have hm : a - j (g₁ a) ∈ RingHom.ker g₂ := by
    rw [ker_eq_maximalIdeal j g₂ h₂, ← ker_eq_maximalIdeal j g₁ h₁, RingHom.mem_ker, map_sub,
      show g₁ (j (g₁ a)) = g₁ a from RingHom.congr_fun h₁ (g₁ a), sub_self]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  rw [hm]
  exact (RingHom.congr_fun h₂ (g₁ a)).symm

theorem tangent_eq_stalk_dual : ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (x₀ : A.left), x₀ ∈ Set.range (η[A]).left.base →
    ∃ jk : k →+* A.left.presheaf.stalk x₀,
      (∀ a : A.left.presheaf.stalk x₀, ∃ c : k, a - jk c ∈ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀)) ∧
      (∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k (DualNumber k) →
        ∃ v : epsR k ⟶ A, IsTangent v ∧ v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ∧
      (∀ ψ₁ ψ₂ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ₁.comp jk = algebraMap k (DualNumber k) →
        ψ₂.comp jk = algebraMap k (DualNumber k) →
        Spec.map (CommRingCat.ofHom ψ₁) ≫ A.left.fromSpecStalk x₀ = Spec.map (CommRingCat.ofHom ψ₂) ≫ A.left.fromSpecStalk x₀ →
        ψ₁ = ψ₂) := by
  intro k _ A _ x₀ hx
  obtain ⟨pt, rfl⟩ := hx
  have hpt : pt = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  subst hpt
  let s : Sp k ⟶ A.left := (η[A]).left
  have hsA : s ≫ A.hom = 𝟙 _ := (η[A]).w.trans rfl
  have hr : Spec.map (Scheme.stalkClosedPointTo s) ≫ A.left.fromSpecStalk _ = s :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  have hJ := Spec.map_preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom)

  set r := Scheme.stalkClosedPointTo s with hrdef
  set J := Spec.preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom) with hJdef
  have hrJ : J ≫ r = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hJ, ← Category.assoc, hr, hsA, Spec.map_id]
  have hcomp : r.hom.comp J.hom = RingHom.id k := congrArg CommRingCat.Hom.hom hrJ
  have hfst : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
      ψ.comp J.hom = algebraMap k (DualNumber k) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ψ).comp J.hom = RingHom.id k := by
    intro ψ hψ
    rw [RingHom.comp_assoc, hψ]
    ext c
    simp
  refine ⟨J.hom, fun a => ⟨r.hom a, ?_⟩, fun ψ hψ => ?_, fun ψ₁ ψ₂ h₁ h₂ h => ?_⟩
  · rw [← ker_eq_maximalIdeal J.hom r.hom hcomp, RingHom.mem_ker, map_sub,
      show r.hom (J.hom (r.hom a)) = r.hom a from RingHom.congr_fun hcomp _, sub_self]
  · refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _) ?_, ?_, rfl⟩
    · show Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      rw [← hJ, ← Spec.map_comp, ← hψ]
      rfl
    · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ = s
      rw [← Category.assoc, ← Spec.map_comp, ← hr]
      congr 2
      ext1
      exact ringHom_eq_of_comp_eq_id J.hom _ _ (hfst ψ hψ) hcomp
  · have hloc : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
        ψ.comp J.hom = algebraMap k (DualNumber k) → IsLocalHom ψ := by
      intro ψ hψ
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [← ker_eq_maximalIdeal J.hom _ (hfst ψ hψ), RingHom.mem_ker] at hm
      have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 ha
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply] at hm
      rw [hm] at hu
      exact not_isUnit_zero hu
    have e1 := hloc ψ₁ h₁
    have e2 := hloc ψ₂ h₂
    have hinj := (SpecToEquivOfLocalRing A.left (CommRingCat.of (DualNumber k))).symm.injective
      (a₁ := ⟨_, CommRingCat.ofHom ψ₁, e1⟩) (a₂ := ⟨_, CommRingCat.ofHom ψ₂, e2⟩) h
    have := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    exact congrArg (fun f => f.1.hom) this
end GlobalTheory.TangentStalk
end
end

