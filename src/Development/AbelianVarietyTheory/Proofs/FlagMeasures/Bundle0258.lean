module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimeSqLeLocalHermitianDualIndex
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.IdxLower

theorem prime_le_relIndex {G : Type*} [AddCommGroup G] (H K : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : H.relIndex K ≠ 0) (hk : ∃ k ∈ K, k ∉ H) (hkill : ∀ k ∈ K, T • k ∈ H) :
    T ≤ H.relIndex K := by
  classical
  obtain ⟨k, hkK, hkH⟩ := hk
  have hq0 : (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) ≠ 0 := by
    intro h
    apply hkH
    have := (QuotientAddGroup.eq_zero_iff _).1 h
    simpa [AddSubgroup.mem_addSubgroupOf] using this
  have hqT : T • (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hkill k hkK
  have hord : addOrderOf (((⟨k, hkK⟩ : K) : K ⧸ H.addSubgroupOf K)) = T := by
    rcases hT.eq_one_or_self_of_dvd _ (addOrderOf_dvd_of_nsmul_eq_zero hqT) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hq0
    · exact h
  have hdvd : T ∣ H.relIndex K := by
    rw [← hord, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    exact addOrderOf_dvd_natCard _
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd

theorem sq_le_relIndex {G : Type*} [AddCommGroup G] (A B C : AddSubgroup G) (T : ℕ) (hT : T.Prime)
    (h0 : A.relIndex B ≠ 0) (hAC : A ⊓ B ≤ C) (hCB : C ≤ B) (h1 : ∃ k ∈ B, k ∉ C)
    (h2 : ∃ k ∈ C, k ∉ A) (hkill : ∀ k ∈ B, T • k ∈ A) :
    T ^ 2 ≤ A.relIndex B := by
  have hmid : (A ⊓ B).relIndex C = A.relIndex C := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ B) C, ← AddSubgroup.inf_relIndex_right A C,
      inf_assoc, inf_eq_right.2 hCB]
  have hAB : A.relIndex B = A.relIndex C * C.relIndex B := by
    rw [← AddSubgroup.inf_relIndex_right A B, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hAC hCB, hmid]
  have hAC0 : A.relIndex C ≠ 0 := by
    intro h; apply h0; rw [hAB, h, zero_mul]
  have hCB0 : C.relIndex B ≠ 0 := by
    intro h; apply h0; rw [hAB, h, mul_zero]
  have hle1 : T ≤ A.relIndex C := prime_le_relIndex A C T hT hAC0 h2 (fun k hk => hkill k (hCB hk))
  have hle2 : T ≤ C.relIndex B := prime_le_relIndex C B T hT hCB0 h1
    (fun k hk => hAC (AddSubgroup.mem_inf.2 ⟨hkill k hk, B.nsmul_mem hk T⟩))
  rw [hAB, sq]
  exact Nat.mul_le_mul hle1 hle2

theorem nsmul_mem_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (L M : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ x ∈ M, T • x ∈ L) : ∀ y ∈ loc v M, T • y ∈ loc v L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨T • m, h m hm, ?_⟩
    funext i
    simp
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem nsmul_mem_of_dual {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (h : ∀ y ∈ dualSet (σ : E →+* E) J L, (T : E) • y ∈ L) : ∀ x ∈ dualL σ J L, T • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => rw [← Nat.cast_smul_eq_nsmul E]; exact h y hy
  | zero => rw [smul_zero]; exact L.zero_mem
  | add x z _ _ hx hz => rw [smul_add]; exact L.add_mem hx hz
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem a hx

theorem sq_le_local_index : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ((∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) ↔ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2)) → (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ≠ 0 → T ^ 2 ≤ (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT hsplit hrank hTL v hv sp hsp h1 hiff h0
  classical
  obtain ⟨_, _, hkillT, _, hnt⟩ := hTL
  have hkill : ∀ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, T • k ∈ (loc v L).toAddSubgroup :=
    fun k hk => nsmul_mem_loc v L (dualL cm.sig J L) T (nsmul_mem_of_dual cm.sig J L T hkillT) k hk
  obtain ⟨x, hxB, hxA⟩ := hnt v hv
  have hsc := split_components F E cm n J hJ hdet v sp hsp h1
  have hnot1 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1) := by
    intro hP1
    exact hxA ((hsc.1 L x).2 ⟨hP1 x hxB, hiff.1 hP1 x hxB⟩)
  have hnot2 : ¬ (∀ y ∈ loc v (dualL cm.sig J L), ∃ z ∈ loc v L, ∀ b, (sp (z b)).2 = (sp (y b)).2) :=
    fun hP2 => hnot1 (hiff.2 hP2)
  push Not at hnot1 hnot2
  obtain ⟨y1, hy1B, hy1⟩ := hnot1
  obtain ⟨y2, hy2B, hy2⟩ := hnot2
  have heV : sp.symm (0, 1) ∈ intV E v := by
    have hI := (split_integral_local F E v sp h1 (sp.symm (0, 1))).2
    rw [RingEquiv.apply_symm_apply] at hI
    exact hI ⟨zero_mem _, one_mem _⟩
  have hcomp : ∀ b, sp (((⟨sp.symm (0, 1), heV⟩ : intV E v) • y2) b) = (0, (sp (y2 b)).2) := by
    intro b
    show sp (sp.symm (0, 1) * y2 b) = _
    rw [map_mul, RingEquiv.apply_symm_apply]
    ext <;> simp
  let C : AddSubgroup (Fin n → E ⊗[F] v.adicCompletion F) :=
    { carrier := {y | y ∈ loc v (dualL cm.sig J L) ∧ ∃ z ∈ loc v L, ∀ b, (sp (z b)).1 = (sp (y b)).1}
      add_mem' := by
        intro a c ha hc
        obtain ⟨ha, za, hza, hza'⟩ := ha
        obtain ⟨hc, zc, hzc, hzc'⟩ := hc
        refine ⟨Submodule.add_mem _ ha hc, za + zc, Submodule.add_mem _ hza hzc, fun b => ?_⟩
        simp only [Pi.add_apply, map_add (f := _), Prod.fst_add, hza', hzc']
      zero_mem' := by
        refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun b => rfl⟩
      neg_mem' := by
        intro a ha
        obtain ⟨ha, za, hza, hza'⟩ := ha
        refine ⟨Submodule.neg_mem _ ha, -za, Submodule.neg_mem _ hza, fun b => ?_⟩
        simp only [Pi.neg_apply, map_neg, Prod.fst_neg, hza'] }
  have hAC : (loc v L).toAddSubgroup ⊓ (loc v (dualL cm.sig J L)).toAddSubgroup ≤ C := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := AddSubgroup.mem_inf.1 hy
    exact ⟨hyB, y, hyA, fun b => rfl⟩
  have hCB : C ≤ (loc v (dualL cm.sig J L)).toAddSubgroup := fun y hy => hy.1
  have hBC : ∃ k ∈ (loc v (dualL cm.sig J L)).toAddSubgroup, k ∉ C := by
    refine ⟨y1, hy1B, fun hC => ?_⟩
    obtain ⟨z, hz, hz'⟩ := hC.2
    obtain ⟨b, hb⟩ := hy1 z hz
    exact hb (hz' b)
  have hCA : ∃ k ∈ C, k ∉ (loc v L).toAddSubgroup := by
    refine ⟨(⟨sp.symm (0, 1), heV⟩ : intV E v) • y2,
      ⟨Submodule.smul_mem _ _ hy2B, 0, Submodule.zero_mem _, fun b => ?_⟩, fun hA => ?_⟩
    · rw [hcomp b]; simp
    · obtain ⟨b, hb⟩ := hy2 _ hA
      apply hb
      rw [hcomp b]
  exact sq_le_relIndex _ _ C T hT h0 hAC hCB hBC hCA hkill

end GlobalTheory.St.G.IdxLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalRelIndexDvdHermitianDual
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.GlobIdx

theorem prod_relIndex_dvd {G ι : Type} [AddCommGroup G] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    (B A : AddSubgroup G) (H K : ∀ i, AddSubgroup (M i)) (φ : ∀ i, G →+ M i) (S : Finset ι)
    (hA : ∀ i, ∀ x ∈ A, φ i x ∈ K i) (hB : ∀ i, ∀ x ∈ B, φ i x ∈ H i)
    (hs : ∀ y : ∀ i, M i, (∀ i, y i ∈ K i) → ∃ x ∈ A, ∀ i ∈ S, φ i x - y i ∈ H i) :
    ∏ i ∈ S, (H i).relIndex (K i) ∣ B.relIndex A := by
  classical
  let ψ : A →+ (∀ i : S, K i ⧸ (H i).addSubgroupOf (K i)) :=
    AddMonoidHom.pi fun i : S => (QuotientAddGroup.mk' ((H i).addSubgroupOf (K i))).comp
      (((φ i).comp A.subtype).codRestrict (K i) fun x => hA i x x.2)
  have hψ : Function.Surjective ψ := by
    intro q
    choose r hr using fun i : S => QuotientAddGroup.mk_surjective (q i)
    obtain ⟨x, hx, h⟩ := hs (fun i => if hi : i ∈ S then (r ⟨i, hi⟩ : M i) else 0) (fun i => by
      by_cases hi : i ∈ S
      · simp only [hi, dif_pos]; exact (r ⟨i, hi⟩).2
      · simp only [hi, dif_neg, not_false_eq_true]; exact zero_mem _)
    refine ⟨⟨x, hx⟩, funext fun i => ?_⟩
    rw [← hr i]
    have h1 := h i i.2
    simp only [i.2, dif_pos] at h1
    show (QuotientAddGroup.mk (⟨φ i x, hA i x hx⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = _
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
    exact h1
  have hker : B.addSubgroupOf A ≤ ψ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    funext i
    show (QuotientAddGroup.mk (⟨φ i x, hA i x x.2⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hB i x hx
  have h1 : ψ.ker.index ∣ B.relIndex A := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hψ, AddSubgroup.card_top, Nat.card_pi] at h1
  rw [← Finset.prod_coe_sort S]
  exact h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L D : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ D, T • y ∈ L) : ∀ z ∈ loc v D, T • z ∈ loc v L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨T • y, h y hy, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prod_loc_relIndex_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL S _
  obtain ⟨hlat, -, hTL, -, -⟩ := hL
  have hfin := (GlobalTheory.St.G.dualL_local_adelic F E cm n J hJ hdet L hlat).1.1
  have hTD : ∀ y ∈ dualL cm.sig J L, T • y ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact hTL x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  refine prod_relIndex_dvd (M := fun v : HeightOneSpectrum (𝓞 F) => Fin n → E ⊗[F] v.adicCompletion F)
    L.toAddSubgroup (dualL cm.sig J L).toAddSubgroup (fun v => (loc v L).toAddSubgroup)
    (fun v => (loc v (dualL cm.sig J L)).toAddSubgroup)
    (fun v => AddMonoidHom.compLeft (inclE (F := F) (E := E) (v.adicCompletion F)).toAddMonoidHom (Fin n)) S
    (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) ?_
  intro y hy
  obtain ⟨x, hx, h⟩ := GlobalTheory.OverCompare.exists_lattice_approx_all F E n (dualL cm.sig J L) hfin T hT.ne_zero y hy
  refine ⟨x, hx, fun v _ => ?_⟩
  obtain ⟨z, hz, e⟩ := h v
  have h1 := nsmul_mem_loc v T L _ hTD z hz
  have e2 : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v = -(T • z) := by
    rw [e]; abel
  show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v ∈ loc v L
  rw [e2]
  exact neg_mem h1

end GlobalTheory.St.G.GlobIdx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeTransportBlockModel
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot

theorem hsDist_equiv_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : hsDist (hf.equiv.symm k) = Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  have h' : Formalism.MainNotions.S.uMat k - 1 = Matrix.reindex f f (UpqT.mat (hf.equiv.symm k) - 1) := by
    rw [show Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.umat k from rfl, h]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  unfold hsDist Formalism.REAL.hs
  rw [h']
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  symm
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← f.sum_comp]
  simp

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c) :
    0 < c := by
  have hV : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hneg'
  have hneg : c ≤ 0 := not_lt.1 hneg'
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2)
        ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) < r := hr
    exact div_nonpos_iff.2 (Or.inr ⟨mul_nonpos_iff.2 (Or.inr ⟨hneg, ENNReal.toReal_nonneg⟩),
      (pow_pos hr' _).le⟩)
  have := le_of_tendsto hc hle
  linarith

private theorem tendsto_gauge_ratio_volume_ball {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (hc : GlobalTheory.Count.IsGauge ε c)
    (hc0 : 0 < c) :
    Tendsto (fun r : ℝ =>
        c * (Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2}).toReal / r ^ (n ^ 2))
      (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  set A : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1)) ≤ r} with hAdef
  set B : ℝ → ℝ≥0∞ := fun r =>
    Formalism.REAL.muG ε {g | Formalism.REAL.hs (Formalism.MainNotions.S.uMat g - 1) < r ^ 2} with hBdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hc' : Tendsto (fun r => c * (A r).toReal / r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 V) := hc
  have hBA : ∀ r : ℝ, 0 < r → B r ≤ A r := by
    intro r hr
    apply measure_mono
    intro g hg
    exact ((Real.sqrt_lt' hr).2 hg).le
  have hAB : ∀ r s : ℝ, 0 < r → s < r → A s ≤ B r := by
    intro r s hr hs
    apply measure_mono
    intro g hg
    exact (Real.sqrt_lt' hr).1 (lt_of_le_of_lt hg hs)
  have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), A r ≠ ⊤ := by
    filter_upwards [hc'.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have h1 : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2)) (𝓝 0) (𝓝 ((1 - 0) ^ (n ^ 2))) :=
      ((continuous_const.sub continuous_id).pow _).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have : Tendsto (fun r : ℝ => (1 - r) * r) (𝓝 0) (𝓝 ((1 - 0) * 0)) :=
        ((continuous_const.sub continuous_id).mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact mul_pos (by linarith [hr.2]) hr.1
  have hlow : Tendsto (fun r : ℝ => (1 - r) ^ (n ^ 2) *
      (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2))) (𝓝[>] 0) (𝓝 V) := by
    simpa using h1.mul (hc'.comp h2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hc' ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hfin] with r hr hAr
    have hr0 : 0 < r := hr.1
    have h1r : 0 < 1 - r := by linarith [hr.2]
    have hBfin : B r ≠ ⊤ := ne_top_of_le_ne_top hAr (hBA r hr0)
    have hle : (A ((1 - r) * r)).toReal ≤ (B r).toReal :=
      ENNReal.toReal_mono hBfin (hAB r _ hr0 (by nlinarith))
    have hne1 : (1 - r) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ h1r.ne'
    have hne2 : r ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hr0.ne'
    have heq : (1 - r) ^ (n ^ 2) * (c * (A ((1 - r) * r)).toReal / ((1 - r) * r) ^ (n ^ 2)) =
        c * (A ((1 - r) * r)).toReal / r ^ (n ^ 2) := by
      rw [mul_pow]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hc0.le) (pow_pos hr0 _).le
  · filter_upwards [self_mem_nhdsWithin, hfin] with r hr hAr
    have hr0 : (0 : ℝ) < r := hr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hAr (hBA r hr0)) hc0.le) (pow_pos hr0 _).le

theorem gauge_transport : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  intro n ε c P Q f hf hc
  have hc0 : 0 < c := pos_of_isGauge' hc
  refine ⟨hc0, ?_⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have hPQ : P + Q = n := Sorts.add_eq f
  have hVfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal with hVdef
  have hV : 0 < V :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' hVfin
  have hlim := tendsto_gauge_ratio_volume_ball hc hc0
  have key : ∀ r : ℝ, ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) {g | hsDist g < r ^ 2} =
      ENNReal.ofReal c * Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} := by
    intro r
    rw [Measure.map_apply (show Measurable (hf.equiv.symm : Formalism.REAL.UJ ε → UpqT P Q) from
        hf.equiv.symm.continuous.measurable)
      (measurableSet_lt continuous_hsDist.measurable measurable_const), Measure.smul_apply, smul_eq_mul]
    congr 2
    ext k
    simp [hsDist_equiv_symm hf k]
  have hBfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2} ≠ ⊤ := by
    filter_upwards [hlim.eventually (lt_mem_nhds hV)] with r hr htop
    rw [htop] at hr
    simp at hr
  have hlim' : Tendsto (fun r : ℝ => ENNReal.ofReal
      (c * (Formalism.REAL.muG ε {k | Formalism.REAL.hs (Formalism.MainNotions.S.uMat k - 1) < r ^ 2}).toReal / r ^ (n ^ 2) / V))
      (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (hlim.div_const V)
    rwa [div_self hV.ne', ENNReal.ofReal_one] at this
  unfold HasEuclDensity
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hBfin] with r hr hB
  have hr0 : (0 : ℝ) < r := hr
  have hball : ballVol ((P + Q) ^ 2) r = ENNReal.ofReal (r ^ (n ^ 2)) * ENNReal.ofReal V := by
    have := ballVol_mul ((P + Q) ^ 2) r 1 hr0 one_pos
    rw [mul_one] at this
    rw [this, hPQ, hVdef, ENNReal.ofReal_toReal hVfin]
    rfl
  rw [key r, hball, ← ENNReal.ofReal_mul (pow_nonneg hr0.le _), div_div,
    ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr0 _) hV), ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_toReal hB]

end GlobalTheory.GaugeQuot
end
end

