module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory
  Matrix
open scoped TensorProduct InnerProductSpace Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultFinite

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

def pt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

theorem mem_sm {τ : D.what₂.Tau} {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem sigma_mem_sm {τ : D.what₂.Tau} (w : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : M.σ τ g w ∈ M.sm τ :=
  mem_sm.2 (sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (mem_sm.1 w.2) hg)

theorem map_sigma {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) (w : M.sm τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ UJset (M.ε τ)) :
    T (Function.update v τ ⟨M.σ τ g w, sigma_mem_sm w hg⟩) = rTr V (pt θ M τ g) (T (Function.update v τ w)) := by
  have := hT.equiv τ _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) (Function.update v τ w)
    ⟨M.σ τ g w, sigma_mem_sm w hg⟩ (by
      rw [Function.update_self]
      exact (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L w) (trRep_conj (σ := M.σ τ) (M.fr_unit τ) g)).symm)
  rwa [Function.update_idem] at this

theorem exists_continuousLinearMap_tens_update {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ a : M.H τ →ₗ[ℂ] (GA D V → ℂ), (∀ w : M.sm τ, a w = T (Function.update v τ w)) ∧
      (∀ x, Sobolev₂ (lieG (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) ((LinearMap.proj x).comp a)) ∧
      ∀ g ∈ UJset (M.ε τ), ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)),
        a (M.σ τ g w) = rTr V (pt θ M τ g) (a w) := by
  obtain ⟨a, ha⟩ := LinearMap.exists_extend (T.toLinearMap v τ)
  have ha' : ∀ w : M.sm τ, a w = T (Function.update v τ w) := fun w => LinearMap.congr_fun ha w
  refine ⟨a, ha', fun x => ?_, fun g hg w hw => ?_⟩
  · obtain ⟨ℓ, ⟨L, C, h1, h2⟩, e⟩ := hT.cont τ v x
    refine ⟨L, C, h1, fun w hw => ?_⟩
    have := h2 w hw
    rw [e ⟨w, mem_sm.2 hw⟩, ← ha'] at this
    exact this
  · rw [ha' ⟨w, mem_sm.2 hw⟩, ← map_sigma hT τ v _ hg, ← ha']

theorem eq_zero_of_apply {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (h₀ : ∀ τ, v₀ τ ≠ 0) (h : T v₀ = 0) :
    T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ = v₀ ρ) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; rw [show v = v₀ from funext fun ρ => hv ρ (by simp), h]
    | insert τ s _ ih =>
      intro v hv
      have h2 : T (Function.update v τ (v₀ τ)) = 0 := by
        refine ih _ fun ρ hρ => ?_
        by_cases hh : ρ = τ
        · subst hh; simp
        · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
      obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
      have := (M.ds τ).1
      funext x
      have h3 := _root_.GlobalTheory.SmVec.sobCont_eq_zero_of_orbit _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 _ (hs x)
        (v₀ τ) (mem_sm.1 (v₀ τ).2) (fun c => h₀ τ (Subtype.ext c)) (fun g hg => by
          show a _ x = 0
          rw [hq g hg _ (mem_sm.1 (v₀ τ).2), e, h2]
          rfl) (v τ) (mem_sm.1 (v τ).2)
      have h4 : a (v τ) x = 0 := h3
      rwa [e, Function.update_eq_self] at h4
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

def kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) : Representation ℂ (Formalism.REAL.KG ε) W where
  toFun k := (σ (Formalism.REAL.toMK k) : H →ₗ[ℂ] H).restrict fun w hw => hW _ k.2 w hw
  map_one' := by
    ext w
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  map_mul' k k' := by
    ext w
    show σ (Formalism.REAL.toMK k * Formalism.REAL.toMK k') w = σ (Formalism.REAL.toMK k) (σ (Formalism.REAL.toMK k') w)
    rw [hσ.1.2 _ (k : Formalism.REAL.UJ ε).2 _ (k' : Formalism.REAL.UJ ε).2]; rfl

theorem isContRep_kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) :
    GlobalTheory.Published.AutFin.IsContRep (kRep hσ W hW) := fun ℓ w =>
  (LinearMap.continuous_of_finiteDimensional ℓ).comp
    (Continuous.subtype_mk ((continuous_orbit hσ w).comp continuous_subtype_val) _)

theorem hcFinite (hP : GlobalTheory.Published.HarishChandraFinite) : HCFinite θ M J χ := by
  rintro hθ ⟨U, hU, hUJ⟩
  have hc := fun τ => (M.ds τ).1
  choose W hWf hW0 hWs hWk using fun τ => _root_.GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    ⟨_, (M.ds τ).2.2.2.2.2.1⟩
  choose c hcs using fun τ => _root_.GlobalTheory.SmVec.GelfScalar.gelfH_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1
  choose u huW hu0 using fun τ => (Submodule.ne_bot_iff _).1 (hW0 τ)
  let v₀ : M.Vec := fun τ => ⟨u τ, mem_sm.2 (hWs τ (huW τ))⟩
  have hfin := hP D θ hθ V U hU M.ε M.fr (fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩) (fun τ => W τ)
    (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) (fun τ => isContRep_kRep _ _ _) c
  have hmem : ∀ T : Mult θ M J χ, (T : MMap M) v₀ ∈ GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c := by
    intro T
    have hT := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2
    refine ⟨hT.aut v₀, fun k hk hf g => ?_, fun τ => ?_, fun τ k => ?_⟩
    · rw [hT.lev v₀ k (hUJ k hk hf).1, (hUJ k hk hf).2, one_mul]
    · obtain ⟨a, e, -, hq⟩ := exists_continuousLinearMap_tens_update hT τ v₀
      have := GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) (kRep (M.ds τ).2.2.1 (W τ) (hWk τ))
        (a.comp (W τ).subtype) (fun k w => hq (Formalism.REAL.toMK k) (GlobalTheory.LowTypeRestriction.kset_subset k.2) w (hWs τ w.2)) ⟨u τ, huW τ⟩
      have e' : (a.comp (W τ).subtype) ⟨u τ, huW τ⟩ = (T : MMap M) v₀ := by
        rw [← Function.update_eq_self τ v₀, ← e]; rfl
      rwa [e'] at this
    · rw [_root_.GlobalTheory.MultGelf.gelf_apply D θ V S M J χ hθ T hT τ k v₀ (c τ k • v₀ τ) (hcs τ k _ (mem_sm.1 (v₀ τ).2)).symm,
        MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl
  let ev : Mult θ M J χ →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c) :=
    { toFun := fun T => ⟨(T : MMap M) v₀, Submodule.subset_span (hmem T)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun T hT => Subtype.ext ?_)
  exact eq_zero_of_apply ((GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2) v₀
    (fun τ h => hu0 τ (congrArg Subtype.val h)) (congrArg Subtype.val hT)

theorem schur_multMap (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {T T' : MMap M} (hT : IsMultMap θ M J χ T)
    (hT' : IsMultMap θ M J χ T') (τ : D.what₂.Tau) (v v' : M.Vec) :
    ∃ c : ℂ, ∀ w w' : M.sm τ,
      ∫ g in 𝓕, star (T (Function.update v τ w) g) * T' (Function.update v' τ w') g ∂μ = c * ⟪w, w'⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have := (M.ds τ).1
  obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
  obtain ⟨a', e', hs', hq'⟩ := exists_continuousLinearMap_tens_update hT' τ v'
  have hpt : Continuous fun g : Formalism.REAL.UJ (M.ε τ) => pt θ M τ (umat g) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
      ((continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const)
      fun g => conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) g.2
  have hf : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a w) ∧ IsCuspFun V (a w) :=
    fun w hw => by rw [e ⟨w, mem_sm.2 hw⟩]; exact ⟨hT.aut _, hT.cusp _⟩
  have hf' : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a' w) ∧ IsCuspFun V (a' w) :=
    fun w hw => by rw [e' ⟨w, mem_sm.2 hw⟩]; exact ⟨hT'.aut _, hT'.cusp _⟩
  have hinv : ∀ (φ ψ : GA D V → ℂ) (k : GA D V), IsAutFunSm θ V φ → IsAutFunSm θ V ψ →
      ∫ x in 𝓕, star (rTr V k φ x) * rTr V k ψ x ∂μ = ∫ x in 𝓕, star (φ x) * ψ x ∂μ := fun φ ψ k hφ hψ =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * ψ x) k h𝓕 fun γ hγ g => by
      rw [hφ.left γ hγ, hψ.left γ hγ]).2
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 (GA D V)
    (μ.restrict 𝓕) (fun g x => x * pt θ M τ (umat g)) (continuous_snd.mul (hpt.comp continuous_fst)) a a'
    (fun w hw => ⟨(hf w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf w hw).1 (hf w hw).2,
      fun g x => congrFun (hq _ g.2 w hw) x⟩) hs
    (fun w hw => ⟨(hf' w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf' w hw).1 (hf' w hw).2,
      fun g x => congrFun (hq' _ g.2 w hw) x⟩) hs'
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf w hw).1)
    (fun g hg u hu w hw => by rw [hq' g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf' u hu).1 (hf' w hw).1)
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf' w hw).1)
  refine ⟨c, fun w w' => ?_⟩
  rw [← e, ← e']
  exact hc w (mem_sm.1 w.2) w' (mem_sm.1 w'.2)

theorem schurMult (hP : GlobalTheory.Published.CuspRapidDecay) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    SchurMult θ M J χ μ 𝓕 := by
  intro hθ hμ h𝓕 T hT T' hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' D.what₂.Tau (fun τ => M.sm τ) (fun v v' => ∫ g in 𝓕, star (T v g) * T' v' g ∂μ)
    fun τ v v' => schur_multMap hP hθ hμ h𝓕 hT hT' τ v v'
  exact ⟨c, fun v v' => ⟨GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hμ h𝓕 (hT.aut v)
    (hT'.aut v') (hT'.cusp v'), hc v v'⟩⟩

theorem hcFinite_and_schurMult : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
      (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      HCFinite θ M J χ ∧ SchurMult θ M J χ μ 𝓕 :=
  fun h h' _ _ _ _ _ _ _ μ 𝓕 => ⟨hcFinite h, schurMult h' μ 𝓕⟩

end GlobalTheory.MultFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitian
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3

theorem liftForm_inner_eq_hform : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB i t x y
  have h1 : ∀ f g : (A.MtCSD i t).Forms, ⟪R.jV i t f, R.jV i t g⟫_ℂ = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
    intro f g
    refine ((hB.models.HV i t).2.2 _ _).trans ?_
    refine (congrArg₂ _ (hB.models.jV i t f) (hB.models.jV i t g)).trans ?_
    exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g
  have h2 := GlobalTheory.Mem.LiftForms.csum_lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x y
  have h3 : ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ =
      D.what₂.embLL ((Nat.card (A.fam.lvlA F.P0 F.ψ0).P : D.what₂.LL) * Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) :=
    (h1 (liftForm A F.P0 F.ψ0 i t x) (liftForm A F.P0 F.ψ0 i t y)).trans (congrArg D.what₂.embLL h2)
  have hP : RealDat.nP F false = (Nat.card F.P0 : ℝ) := rfl
  have hc : (Nat.card F.P0 : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F.P0)).ne'
  rw [h3, map_mul, map_natCast, hP, ← mul_assoc]
  change ((((Nat.card F.P0 : ℝ))⁻¹ : ℝ) : ℂ) * (Nat.card F.P0 : ℂ) * _ = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSum
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.TopGram


set_option maxHeartbeats 4000000 in
theorem topGram : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hW b t x y
  have hHX := (hW.models.HX t).2.2
  have hjX := hW.models.jX t
  rw [hHX, hjX, hjX]
  have hiso := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.2
  have key : ∀ f f' : A.fam.amb.FR t, Bridge.adInner (Bridge.ratF D.sp.X') (levEnv D.sp.X' R.βX (R.datXt t)).J
      (R.B.R t).pres.y (R.B.jR t f) (R.B.jR t f') = D.what₂.embLL ((A.fam.R t).S.csum f f') := fun f f' => hiso f f'
  have hr : ∀ z, rowForm A (F.lvl b).P (F.lvl b).ψ t z =
      GlobalTheory.Mem.LiftForms.lvlForm (A.fam.R t).S (A.fam.R t).r (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P
        (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).ψ z := fun z => rfl
  refine (congrArg (fun z => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * z) (key (rowForm A (F.lvl b).P (F.lvl b).ψ t x) (rowForm A (F.lvl b).P (F.lvl b).ψ t y))).trans ?_
  rw [hr, hr, GlobalTheory.Mem.LiftForms.csum_lvlForm]
  have hc : (Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  have hn : (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) = ((Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv]
    rfl
  rw [map_mul, map_natCast, hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end GlobalTheory.Mem.TopGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB → interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.VB.interNum_one_eq_genRank_mul | exact GlobalTheory.VB.interNum_one_eq_genRank_mul | (intros; apply GlobalTheory.VB.interNum_one_eq_genRank_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

def domGram (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 - Matrix.of x * (Matrix.of x)ᴴ)⁻¹)ᵀ

def IsNegSq {E : Type*} [AddCommGroup E] [Module ℂ E] {m : ℕ} (F : E → E → Matrix (Fin m) (Fin m) ℂ) (r : ℕ) : Prop :=
  ∃ (S : Matrix (Fin m) (Fin m) ℂ) (T : E →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det ∧
    ∀ ξ η, F ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S

def sqPoly {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C ((T (coordVec a) * (T (coordVec b))ᴴ) i j) * X (a, b)

end GlobalTheory.PointFormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelVectorSumOfIsotypicPieces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.DecompKer

open Formalism.L2.NG (FinTyp)

def isoSetoid (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Setoid (FinTyp L n) where
  r π π' := π.Iso π'
  iseqv := ⟨fun π => Formalism.L2.NG.IsoRep.refl _, fun {π _} h => Formalism.L2.NG.IsoRep.symm π.stable h,
    fun h h' => Formalism.L2.NG.IsoRep.trans h h'⟩

theorem isotIn_le_of_iso {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) {π π' : FinTyp D.host.E n}
    (h : π.Iso π') : principalLevelFrame.isotIn (D := D) ρ C π' ≤ principalLevelFrame.isotIn (D := D) ρ C π := by
  obtain ⟨T, hT⟩ := h
  refine iSup₂_le fun Φ hΦ => ?_
  rintro _ ⟨f, rfl⟩
  have hE : principalLevelFrame.IsEqvA ρ π (Φ.comp T.toLinearMap) ∧ LinearMap.range (Φ.comp T.toLinearMap) ≤ C := by
    refine ⟨fun g a => ?_, ?_⟩
    · have e : T ⟨Formalism.L2.NG.rt D.host.E n g a, π.stable g a a.2⟩ =
          ⟨Formalism.L2.NG.rt D.host.E n g (T a), π'.stable g _ (T a).2⟩ :=
        Subtype.ext (hT g a _ rfl)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [e]
      exact hΦ.1 g (T a)
    · rintro _ ⟨a, rfl⟩
      exact hΦ.2 ⟨T a, rfl⟩
  refine Submodule.mem_iSup_of_mem (Φ.comp T.toLinearMap) (Submodule.mem_iSup_of_mem hE ⟨T.symm f, ?_⟩)
  simp

end GlobalTheory.DecompKer


open GlobalTheory.DecompKer in
theorem GlobalTheory.decomp_kernels_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, ∀ y ∈ principalLevelFrame.isotIn (D := D) ρ C π', B x y = 0) → ∀ (ι : Type) (O : ι → A →ₗ[ℂ] A), (∀ i π, ∀ x ∈ principalLevelFrame.isotIn (D := D) ρ C π, O i x ∈ principalLevelFrame.isotIn (D := D) ρ C π) → ∀ x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π, (∀ i, O i x = 0) → x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, (principalLevelFrame.isotIn (D := D) ρ C π ⊓ ⨅ i, LinearMap.ker (O i)) := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 ι O hO x hx hOx
  classical
  let S := isoSetoid D.host.E n
  let q : Formalism.L2.NG.FinTyp D.host.E n → Quotient S := Quotient.mk S
  have hC : ∀ π, principalLevelFrame.isotIn (D := D) ρ C π ≤ C := fun π => iSup₂_le fun Φ h => h.2
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx
  set t := f.support.image q with ht
  let y : Quotient S → A := fun c => ∑ π ∈ f.support with q π = c, f π
  have hxy : (f.sum fun _ xi => xi) = ∑ c ∈ t, y c := by
    rw [Finsupp.sum]
    exact (Finset.sum_fiberwise_of_maps_to (fun π hπ => Finset.mem_image_of_mem q hπ) _).symm
  have hrep : ∀ π c, q π = c → c.out.Iso π := fun π c hq =>
    Quotient.exact (s := S) (by rw [Quotient.out_eq]; exact hq.symm)
  have hyI : ∀ c, y c ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := by
    intro c
    refine Submodule.sum_mem _ fun π hπ => ?_
    exact isotIn_le_of_iso ρ C (hrep π c (Finset.mem_filter.mp hπ).2) (hf π)
  have hni : ∀ c c' : Quotient S, c ≠ c' → ¬ c.out.Iso c'.out := by
    intro c c' hne hI
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound hI
  have hB0 : ∀ u ∈ C, B u 0 = 0 := by
    intro u hu
    have := h1 u hu 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this
  have hOy : ∀ i, ∀ c ∈ t, O i (y c) = 0 := by
    intro i c hc
    set u := O i (y c) with hu
    have huI : u ∈ principalLevelFrame.isotIn (D := D) ρ C c.out := hO i c.out (y c) (hyI c)
    have huC : u ∈ C := hC _ huI

    let Z : Submodule ℂ A :=
      { carrier := {v | v ∈ C ∧ B u v = 0}
        zero_mem' := ⟨C.zero_mem, hB0 u huC⟩
        add_mem' := fun {a b} ha hb => ⟨C.add_mem ha.1 hb.1, by
          have := h1 u huC a ha.1 b hb.1 1
          rw [one_smul] at this
          rw [this, ha.2, hb.2]; simp⟩
        smul_mem' := fun c' a ha => ⟨C.smul_mem c' ha.1, by
          have := h1 u huC 0 C.zero_mem a ha.1 c'
          rw [zero_add] at this
          rw [this, hB0 u huC, ha.2]; simp⟩ }
    have hsum : ∑ c' ∈ t, O i (y c') = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hxy]; exact hOx i
    have hrest : ∑ c' ∈ t.erase c, O i (y c') ∈ Z := by
      refine Submodule.sum_mem _ fun c' hc' => ?_
      have hne : c' ≠ c := (Finset.mem_erase.mp hc').1
      have hv : O i (y c') ∈ principalLevelFrame.isotIn (D := D) ρ C c'.out := hO i c'.out (y c') (hyI c')
      exact ⟨hC _ hv, h4 c.out c'.out (hni c c' (Ne.symm hne)) u huI _ hv⟩
    have hueq : u = -∑ c' ∈ t.erase c, O i (y c') := by
      rw [eq_neg_iff_add_eq_zero, hu, Finset.add_sum_erase t (fun c' => O i (y c')) hc, hsum]
    have huZ : u ∈ Z := by rw [hueq]; exact Z.neg_mem hrest
    by_contra hne
    have := h3 u huC hne
    rw [huZ.2] at this
    simp at this
  rw [hxy]
  refine Submodule.sum_mem _ fun c hc => ?_
  refine Submodule.mem_iSup_of_mem c.out (Submodule.mem_inf.mpr ⟨hyI c, ?_⟩)
  exact Submodule.mem_iInf _ |>.mpr fun i => LinearMap.mem_ker.mpr (hOy i c hc)
end

