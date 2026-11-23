module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem serre_one {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (F : X.Modules) (hF : IsCoherent F) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  letI := algebraOfOver X A
  haveI : GlobalTheory.QCoh.IsFiniteQC F := ⟨hF.1, hF.2⟩
  exact Filter.eventually_atTop.1 (GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := X ↘ Spec (.of A)) (fun _ => rfl) F hH)

theorem kerOpSeq (hG : GradedNoeth) {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    ∃ d₁ : ℕ, OpSeq k (kerSeq M T) (kerOps hM.comm) d₁ := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  choose D hD using fun U : X.affineOpens => GlobalTheory.T.kernel_operators_eventually_generate hG hM U
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => U.1.isOpen) (fun x _ => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨U, hU⟩)
  have hcoh : ∀ e, IsCoherent (kerSeq M T e) := fun e => by
    haveI := (hM.coherent (e + 1)).1
    exact isCoherent_kernel _ (hM.coherent e)
  refine ⟨t.sup D, ⟨hcoh, kerOps_comm hM.comm, fun e he => ?_⟩⟩
  refine _root_.GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local (fun i => (hcoh e).1) (hcoh (e + 1)).1 _ (fun x => ?_)
  obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨U, hxU, hD U e ((Finset.le_sup hUt).trans he)⟩

theorem vanish_of_ker_cok {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    {M : ℕ → X.Modules} (τ : ∀ e, M e ⟶ M (e + 1)) (n : ℤ)
    (h0 : ∀ q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M 0) H n) q))
    (hK : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (kernel (τ e)) H n) q))
    (hC : ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (cokernel (τ e)) H n) q)) :
    ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    intro q hq
    have hL := GlobalTheory.Twist.isLB_lbZPow hH n
    let f := τ e
    let S₁ : ShortComplex X.Modules := ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
      rw [← cancel_mono (Abelian.image.ι f)]; simp)
    have hS₁ : S₁.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _
        (isKernelOfComp (Abelian.image.ι f) f (kernelIsKernel f) _ (Abelian.image.fac f))
    let S₂ : ShortComplex X.Modules := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by
      simp [Abelian.image.ι])
    have hS₂ : S₂.ShortExact := by
      refine { exact := ?_ }
      exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (cokernel.π f))
    have h₁ := GlobalTheory.Twist.shortExact_map hL hS₁
    have h₂ := GlobalTheory.Twist.shortExact_map hL hS₂
    have hIm := GlobalTheory.cohOn.subsingleton₃ h₁ ⊤ q (ih q hq) (hK e (q + 1) (by omega))
    exact GlobalTheory.cohOn.subsingleton₂ h₂ ⊤ q hIm (hC e q hq)

theorem coh_twistZ_of_sections {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB)
    (F : X.Modules) [F.IsQuasicoherent] (h : ∀ U : X.affineOpens, Subsingleton Γ(F, U)) (n : ℤ) (q : ℕ) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) q) := by
  have hz : IsZero F := (GlobalTheory.QCoh.isZero_iff_forall_affine).2 fun U hU => h ⟨U, hU⟩
  have hz' : IsZero (GlobalTheory.twistZ F H n) := (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n)).map_isZero hz
  exact GlobalTheory.cohOn.subsingleton_of_isZero hz' ⊤ q

theorem uniformVanishing (hG : GradedNoeth) : UniformVanishing := by
  intro A _ _ X _ _ H hH k
  induction k with
  | zero =>
    intro M T d hM
    have hz : ∀ e, d < e → ∀ (n : ℤ) q, Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q) := by
      intro e he n q
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      haveI := (hM.coherent (e' + 1)).1
      refine coh_twistZ_of_sections H hH.isLB _ (fun U => ?_) n q
      have := hM.gen e' (by omega) U
      simp only [Set.iUnion_of_empty, Submodule.span_empty] at this
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule Γ(X, U) _) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]
    choose N hN using fun e => serre_one (A := A) H hH (M e) (hM.coherent e)
    obtain ⟨B, hB⟩ := Finite.exists_le (fun i : Fin (d + 1) => N i)
    refine ⟨B, fun n hn e q hq => ?_⟩
    by_cases he : e ≤ d
    · exact hN e n ((hB ⟨e, by omega⟩).trans hn) q hq
    · exact hz e (by omega) n q
  | succ k ih =>
    intro M T d hM
    obtain ⟨d₁, hK⟩ := kerOpSeq hG (A := A) hM
    obtain ⟨a, ha⟩ := ih _ _ _ hK
    obtain ⟨b, hb⟩ := ih _ _ _ (_root_.GlobalTheory.CompanionTheory.GE.UV.cokOpSeq hM)
    obtain ⟨c, hc⟩ := serre_one (A := A) H hH (M 0) (hM.coherent 0)
    refine ⟨max a (max b c), fun n hn => ?_⟩
    exact vanish_of_ker_cok H hH.isLB (T (Fin.last k)) n
      (hc n (by omega)) (fun e q hq => ha n (by omega) e q hq) (fun e q hq => hb n (by omega) e q hq)

end GlobalTheory.CompanionTheory.GE.UV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConjugationMeasureInvariant
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HaarConj

theorem conj_measurePreserving : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (U N : Subgroup G), IsClosed (U : Set G) → (∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) → (∀ n ∈ N, ∃ L : Subgroup G, n ∈ L ∧ L ≤ N ∧ IsCompact (L : Set G)) → ∀ [MeasurableSpace U] [BorelSpace U] (μ : MeasureTheory.Measure U) [μ.IsHaarMeasure], ∀ n ∈ N, ∀ c : U → U, (∀ u, (c u : G) = n * u * n⁻¹) → MeasureTheory.MeasurePreserving c μ μ := by
  intro G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc
  have hninv : n⁻¹ ∈ N := N.inv_mem hn
  let d : U → U := fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩
  have hdc : ∀ u, d (c u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcd : ∀ u, c (d u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcmul : ∀ u v, c (u * v) = c u * c v := fun u v => Subtype.ext (by simp [hc, mul_assoc])
  have hcc : Continuous c := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_
    have : (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹ := funext hc
    rw [this]
    fun_prop
  have hdc' : Continuous d := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : U ≃* U :=
    { toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }
  haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'
  haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨L, hnL, -, hLc⟩ := hL n hn
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds (1 : U)
  let K : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))
  have hK : IsCompact K := (hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)
  let Q' : Set U := Subtype.val ⁻¹' K
  have hQ'c : IsCompact Q' := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQQ' : Q ⊆ Q' := fun q hq =>
    ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩
  have hpos : 0 < μ Q' :=
    (MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')
  have hfin : μ Q' ≠ ⊤ := hQ'c.measure_lt_top.ne
  have hpre : c ⁻¹' Q' = Q' := by
    ext u
    constructor
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = n * (u : G) * n⁻¹ := by
        rw [← hc]
        exact h
      change n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)
      calc n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = n⁻¹ * (l * q * l⁻¹) * n := by group
        _ = (u : G) := by rw [h']; group
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = (u : G) := h
      change n * l * q * (n * l)⁻¹ = (c u : G)
      rw [hc, ← h']
      group
  have hmeas : MeasurableSet Q' := hQ'c.measurableSet
  have h1 : μ.map c Q' = μ Q' := by
    rw [MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]
  have heq := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q'
      = 1 * μ Q' := by
    have h3 := congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq
    simp only [MeasureTheory.Measure.smul_apply, h1] at h3
    rw [one_mul]
    exact h3.symm.trans (by simp [ENNReal.smul_def])
  have hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h2
    exact_mod_cast this
  refine ⟨hcc.measurable, ?_⟩
  rw [heq, hκ, one_smul]

end GlobalTheory.CompanionTheory.HaarConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem conj_perm_entry {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (p q : Fin N) :
    ((GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) (w p) (w q) = (g : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv]
  change ((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd p) < blk (stdBlocks d hd) (wOpen d hd q)) : q < p := by
  by_contra hqp
  have hm := Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)
  change wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm
  unfold wKey at hm
  rw [Prod.Lex.le_iff] at hm
  simp only [ofLex_toLex] at hm
  rcases hm with hlt | ⟨heq, _⟩
  · exact lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)
  · rw [OrderDual.toDual_inj] at heq
    rw [heq] at hb
    exact lt_irrefl _ hb

variable (k : Type) [Field k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

theorem mem_unipU {u : GL (Fin N) k} : u ∈ unipU k d hd ↔
    u ∈ unipB k (Fin N) ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  exact Iff.rfl

theorem conj_mem_parabLower {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹ ∈ parabLower k (stdBlocks d hd) := by
  rw [GlobalTheory.SmGL.mem_parabLower_iff k]
  intro a b i j hab
  obtain ⟨p, hp⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)
  obtain ⟨q, hq⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)
  rw [← hp, ← hq]
  unfold pm
  rw [conj_perm_entry]
  apply ((GlobalTheory.SmGL.mem_unipB k).mp hn).1
  apply lt_of_blk_lt d hd
  rw [hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  exact hab

theorem exists_mul {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u := by
  have hc0 := conj_mem_parabLower k d hd hn
  set P := pm k (wOpen d hd) with hP
  set e := stdBlocks d hd with he
  have hc : P * n * P⁻¹ ∈ parab k (opp e) := hc0
  obtain ⟨v, hv, hcv⟩ := exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩
  set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL
  have hcv' : P * n * P⁻¹ = L * v := hcv
  have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q =
      if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by
    intro p q
    have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q
    simp only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group] at h1
    rw [← h1]
    obtain ⟨⟨x, i⟩, hxi⟩ := e.surjective (wOpen d hd p)
    obtain ⟨⟨y, j⟩, hyj⟩ := e.surjective (wOpen d hd q)
    rw [← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
    split_ifs with hxy
    · subst hxy
      refine (GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_
      refine (GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_
      change ((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _
      rw [hxi, hyj]
      exact conj_perm_entry (wOpen d hd) n p q
    · exact GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j
  have haB : P⁻¹ * L * P ∈ unipB k (Fin N) := by
    rw [GlobalTheory.SmGL.mem_unipB k]
    refine ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hLentry]
      split_ifs
      · exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp
      · rfl
    · rw [hLentry, ite_eq_left rfl]
      exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p
  refine ⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩
  · change P⁻¹ * L * P ∈ unipB k (Fin N) ∧
      P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    refine ⟨haB, ?_⟩
    show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group]
    exact ⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩
  · rw [mem_unipU k d hd]
    refine ⟨?_, ?_⟩
    · have hv' : v = L⁻¹ * (P * n * P⁻¹) := by
        rw [hcv']
        group
      rw [show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn
    · show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e
      rw [show P * (P⁻¹ * v * P) * P⁻¹ = v by group]
      exact hv
  · rw [show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv']
    group

theorem conj_mem_unipU {n u : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) (hu : u ∈ unipU k d hd) :
    n * u * n⁻¹ ∈ unipU k d hd := by
  rw [mem_unipU k d hd] at hu ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩
  have hN := GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)
  have key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ =
      (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) *
        (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹ := by group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hu.2

end GlobalTheory.CompanionTheory.Rodier.OpenFactor

theorem GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn,
    fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCharacterNontrivialOnCell
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RootElt

def elemGL {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) : GL (Fin N) k where
  val := Matrix.transvection i j t
  inv := Matrix.transvection i j (-t)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

theorem elemGL_apply {k : Type} [Field k] {N : ℕ} (i j : Fin N) (hij : i ≠ j) (t : k) (a b : Fin N) :
    (elemGL i j hij t).val a b = (1 : Matrix (Fin N) (Fin N) k) a b + if a = i ∧ b = j then t else 0 := by
  show Matrix.transvection i j t a b = _
  rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun e => h ⟨e.1.symm, e.2.symm⟩]

theorem conj_pm_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (a b : Fin N) :
    (GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹).val a b = g.val (w⁻¹ a) (w⁻¹ b) := by
  rw [← map_inv, Units.val_mul, GroundTheory.Automorphic.mul_permGL_apply, Units.val_mul,
    GroundTheory.Automorphic.permGL_mul_apply]

theorem exists_root_conj_mem_unipRad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)) (i j : Fin N), (j : ℕ) = i + 1 → blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j) → ∀ t : k, ∃ (u : GL (Fin N) k) (hu : u ∈ unipB k (Fin N)), whitChar ψ N ⟨u, hu⟩ = Circle.toUnits (ψ t) ∧ pm k w * u * (pm k w)⁻¹ ∈ unipRad k (stdBlocks d hd) := by
  intro k _ _ _ _ ψ h N d hd w i j hij hb t
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hu : elemGL i j hne t ∈ unipB k (Fin N) := by
    refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [elemGL_apply, Matrix.one_apply_ne hba.ne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hba
      exact absurd hba hlt.not_gt
    · rw [elemGL_apply, Matrix.one_apply_eq, if_neg fun e => hne (e.1.symm.trans e.2), add_zero]
  refine ⟨elemGL i j hne t, hu, ?_, ?_⟩
  · show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (elemGL i j hne t).val p.1 p.2)) = _
    congr 2
    rw [Finset.sum_eq_single_of_mem (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)]
    · rw [elemGL_apply, Matrix.one_apply_ne hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · rintro ⟨a, b⟩ hp hpne
      have hab : (b : ℕ) = a + 1 := (Finset.mem_filter.1 hp).2
      have hne' : a ≠ b := fun e => by rw [e] at hab; omega
      rw [elemGL_apply, Matrix.one_apply_ne hne', if_neg fun e => hpne (Prod.ext e.1 e.2), add_zero]
  · have hent : ∀ a b : Fin N, (pm k w * elemGL i j hne t * (pm k w)⁻¹).val a b =
        (1 : Matrix (Fin N) (Fin N) k) a b + if a = w i ∧ b = w j then t else 0 := by
      intro a b
      rw [conj_pm_apply, elemGL_apply]
      congr 1
      · by_cases e : a = b
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (w⁻¹.injective e')]
      · simp only [Equiv.Perm.inv_eq_iff_eq]
    refine mem_unipRad.2 ⟨mem_parab.2 fun a b hab => ?_, fun c x y => ?_⟩
    · have hne' : a ≠ b := fun e => by rw [e] at hab; exact lt_irrefl _ hab
      rw [hent, Matrix.one_apply_ne hne', if_neg fun e => ?_, add_zero]
      rw [e.1, e.2] at hab
      exact lt_asymm hab hb
    · rw [hent, if_neg fun e => ?_, add_zero]
      · by_cases e : x = y
        · rw [e, Matrix.one_apply_eq, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun e' => e (by simpa using (stdBlocks d hd).injective e')]
      · have h1 := blk_apply (stdBlocks d hd) c x
        have h2 := blk_apply (stdBlocks d hd) c y
        rw [e.1] at h1
        rw [e.2] at h2
        rw [h1, h2] at hb
        exact lt_irrefl _ hb

end GlobalTheory.CompanionTheory.Rodier.RootElt
end
end

