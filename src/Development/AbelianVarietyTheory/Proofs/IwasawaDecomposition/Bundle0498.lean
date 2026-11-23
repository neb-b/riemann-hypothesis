module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SvalEqZeroOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulConjTransposeEq
section
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal Topology

namespace GlobalTheory.BoundedFundDomain

theorem exists_section {G Y : Type} [Group G] [Countable G] [TopologicalSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] (a : G → Y → Y) (hc : ∀ g, Continuous (a g))
    (hmul : ∀ g h y, a (g * h) y = a g (a h y)) (hone : ∀ y, a 1 y = y)
    (hfin : ∀ y, ∃ W ∈ 𝓝 y, {g | a g y ∈ W}.Finite) :
    ∃ F : Set Y, MeasurableSet F ∧ (∀ y, ∃ g, a g y ∈ F) ∧ ∀ y ∈ F, ∀ g, a g y ∈ F → a g y = y := by
  classical
  obtain ⟨B, hB⟩ := ((TopologicalSpace.countable_countableBasis Y).insert ∅).exists_eq_range
    (Set.insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ (TopologicalSpace.countableBasis Y) := hB ▸ Set.mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact TopologicalSpace.isOpen_of_mem_countableBasis h
  let P : ℕ → Y → Prop := fun n y => ∃ g, a g y ∈ B n ∧ ∀ g', a g' y ∈ B n → a g' y = a g y
  have hP : ∀ n g y, P n y → P n (a g y) := by
    rintro n g y ⟨k, hk, hk'⟩
    have e : a (k * g⁻¹) (a g y) = a k y := by rw [← hmul, inv_mul_cancel_right]
    refine ⟨k * g⁻¹, e ▸ hk, fun g' h => ?_⟩
    rw [e, ← hmul] at *
    exact hk' _ h
  have hP' : ∀ n g y, P n (a g y) → P n y := fun n g y h => by
    have := hP n g⁻¹ _ h
    rwa [← hmul, inv_mul_cancel, hone] at this
  have hm : ∀ n g, MeasurableSet {y | a g y ∈ B n} := fun n g => ((hBo n).preimage (hc g)).measurableSet
  have hPm : ∀ n, MeasurableSet {y | P n y} := fun n => by
    simp only [P, Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
    refine MeasurableSet.iUnion fun g => (hm n g).inter (MeasurableSet.iInter fun g' => ?_)
    have := (hm n g').compl.union (isClosed_eq (hc g') (hc g)).measurableSet
    convert this using 1
    ext y
    by_cases h : a g' y ∈ B n <;> simp [h]
  have hex : ∀ y, ∃ n, P n y := fun y => by
    obtain ⟨W, hW, hf⟩ := hfin y
    have hcl : IsClosed (((fun g => a g y) '' {g | a g y ∈ W}) \ {y}) := ((hf.image _).subset Set.sdiff_subset).isClosed
    have hn : W ∩ (((fun g => a g y) '' {g | a g y ∈ W}) \ {y})ᶜ ∈ 𝓝 y :=
      Filter.inter_mem hW (hcl.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨U, hU, hyU, hUW⟩ := (TopologicalSpace.isBasis_countableBasis Y).mem_nhds_iff.1 hn
    obtain ⟨n, rfl⟩ : U ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hU
    refine ⟨n, 1, by rwa [hone], fun g' h => ?_⟩
    rw [hone]
    by_contra hne
    exact (hUW h).2 ⟨⟨g', (hUW h).1, rfl⟩, hne⟩
  refine ⟨⋃ n, B n ∩ ({y | P n y} ∩ ⋂ m, ⋂ _ : m < n, {y | P m y}ᶜ), ?_, fun y => ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hBo n).measurableSet.inter ((hPm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hPm m).compl))
  · have h := Nat.find_spec (hex y)
    obtain ⟨g, hg, -⟩ := id h
    exact ⟨g, Set.mem_iUnion.2 ⟨_, hg, hP _ g y h,
      Set.mem_iInter₂.2 fun m hm h' => Nat.find_min (hex y) hm (hP' _ _ _ h')⟩⟩
  · intro y hy g hg
    obtain ⟨n, h1, h2, h3⟩ := Set.mem_iUnion.1 hy
    obtain ⟨n', h1', h2', h3'⟩ := Set.mem_iUnion.1 hg
    rcases lt_trichotomy n n' with h | rfl | h
    · exact (Set.mem_iInter₂.1 h3' n h (hP _ g _ h2)).elim
    · obtain ⟨k, -, hk⟩ := h2
      rw [hk g h1', ← hk 1 (by rwa [hone]), hone]
    · exact (Set.mem_iInter₂.1 h3 n' h (hP' _ g _ h2')).elim

variable {p q : ℕ}

def majMat (w : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Jpq p q + (2 : ℂ) • (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * (hQ w)⁻¹ *
    (fromRows w (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ)

theorem mul_conjTranspose_eq {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    g.1 * g.1ᴴ = majMat (moeb g.1 0) := by
  have h0 := zero_mem_hcDom p q
  have hu := kapQ_isUnit hg h0
  have h1 := hQ_moeb hg h0
  have h2 := moeb_mul_kapQ hg h0
  have h3 := upq_right hg
  have hd : kapQ g 0 = g.1.toBlocks₂₂ := by simp [kapQ]
  rw [hd] at hu h1 h2
  rw [Matrix.mul_zero, zero_add] at h2
  set w := moeb g.1 0
  set G := g.1
  have h4 : (hQ w)⁻¹ = G.toBlocks₂₂ * G.toBlocks₂₂ᴴ := by
    apply inv_eq_left_inv
    have h5 : G.toBlocks₂₂ᴴ * hQ w * G.toBlocks₂₂ = 1 := by rw [h1]; simp [hQ]
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 h5
  have h6 : fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) * G.toBlocks₂₂ = fromRows G.toBlocks₁₂ G.toBlocks₂₂ := by
    rw [fromRows_mul, h2, Matrix.one_mul]
  rw [majMat, h4, ← h3, ← Matrix.mul_assoc, Matrix.mul_assoc _ G.toBlocks₂₂ᴴ, ← conjTranspose_mul, h6]
  ext a b
  have e : ∀ a c, fromRows G.toBlocks₁₂ G.toBlocks₂₂ a c = G a (Sum.inr c) := by
    rintro (a | a) c <;> rfl
  simp only [Jpq, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, e,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply,
    Matrix.zero_apply]
  simp [Matrix.one_apply]
  ring

theorem continuousAt_majMat {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) : ContinuousAt majMat w := by
  have h : (hQ w).PosDef := hw
  have hQc : Continuous (hQ (p := p) (q := q)) := by unfold hQ; fun_prop
  have h1 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (hQ w)⁻¹) w := by
    refine ContinuousAt.comp (continuousAt_matrix_inv _ ?_) hQc.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h.det_pos.ne'
  have h2 : Continuous fun w : Matrix (Fin p) (Fin q) ℂ => fromRows w (1 : Matrix (Fin q) (Fin q) ℂ) := by
    refine continuous_matrix ?_
    rintro (a | a) c
    · simp only [fromRows_apply_inl]; fun_prop
    · simp only [fromRows_apply_inr]; fun_prop
  have h3 : Continuous fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ =>
      Jpq p q + (2 : ℂ) • (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ) * x.2 *
        (fromRows x.1 (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ) :=
    continuous_const.add ((((h2.comp continuous_fst).matrix_mul continuous_snd).matrix_mul
      (h2.comp continuous_fst).matrix_conjTranspose).const_smul (2 : ℂ))
  have h4 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) w := continuousAt_id.prodMk h1
  exact ContinuousAt.comp (f := fun w : Matrix (Fin p) (Fin q) ℂ => (w, (hQ w)⁻¹)) h3.continuousAt h4

theorem exists_bound {w : Matrix (Fin p) (Fin q) ℂ} (hw : w ∈ hcDom p q) :
    ∃ C : ℝ, ∀ᶠ w' in 𝓝 w, ∀ g ∈ Upq p q, moeb g.1 0 = w' → ∀ a b, ‖g.1 a b‖ ≤ C := by
  have h : ContinuousAt (fun w => ‖(majMat (p := p) (q := q) w).trace‖) w :=
    ((continuous_id.matrix_trace).continuousAt.comp (continuousAt_majMat hw)).norm
  refine ⟨√(‖(majMat w).trace‖ + 1), ?_⟩
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_one _))] with w' hw' g hg e a b
  rw [← e, ← mul_conjTranspose_eq hg] at hw'
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hw'.le)
  have e2 : (g.1 * g.1ᴴ).trace = ((∑ a, ∑ b, ‖g.1 a b‖ ^ 2 : ℝ) : ℂ) := by
    simp [trace, Matrix.mul_apply, Complex.mul_conj']
  rw [e2, Complex.norm_real]
  refine le_trans ?_ (le_abs_self _)
  exact (Finset.single_le_sum (f := fun b => ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖g.1 a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a))

theorem norm_mul_mul_le {n : Type} [Fintype n] (A M B : Matrix n n ℂ) {C : ℝ} (h : ∀ a b, ‖M a b‖ ≤ C) (a b : n) :
    ‖(A * M * B) a b‖ ≤ ∑ d, (∑ c, ‖A a c‖ * C) * ‖B d b‖ := by
  simp only [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h c d) (norm_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem eventually_finite (hp : X.p0 = r - j) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : Pt Tau j (r - j)}
    (hw : w ∈ DomI Tau j (r - j)) :
    ∃ W ∈ 𝓝 w, {γ : GL (Fin r) E | γ ∈ X.Γ ∧ domPt X hj κ (lact γ x) ∈ W}.Finite := by
  choose C hC using fun t => exists_bound (hw t)
  obtain ⟨R, hR⟩ := (Set.finite_range fun s : Tau × Fin r × Fin r =>
    ∑ d, (∑ c, ‖mat (x0F X) (κ s.1) s.2.1 c‖ * C s.1) * ‖(mat x (κ s.1))⁻¹ d s.2.2‖).bddAbove
  refine ⟨_, Filter.eventually_all.2 fun t => (continuous_apply t).continuousAt.eventually (hC t),
    (GlobalTheory.LatFin.finite_automorphisms r X R).subset ?_⟩
  rintro γ ⟨hγ, h⟩
  refine ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩
  obtain ⟨t, rfl⟩ := κ.surjective τ
  obtain ⟨g, hg, e⟩ := exists_upq_of_orth X hj hp (KU.isOrth_lact X hγ hx) (κ t)
  have h1 := h t g hg (by rw [e]; rfl)
  have e2 : γ.1.map (κ t).1 = mat (x0F X) (κ t) * g.1.submatrix (idx hj) (idx hj) * (mat x (κ t))⁻¹ := by
    have hu : IsUnit (mat x (κ t)).det := (ExF.det_ne_of_orth X hx _).isUnit
    rw [e, frameCo, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id,
      mul_nonsing_inv_cancel_left _ _ (det_x0F X _).isUnit]
    exact (mul_nonsing_inv_cancel_right _ _ hu).symm
  have h2 := norm_mul_mul_le (mat (x0F X) (κ t)) (g.1.submatrix (idx hj) (idx hj)) (mat x (κ t))⁻¹
    (fun a b => h1 _ _) a b
  rw [← e2] at h2
  exact h2.trans (hR ⟨(t, a, b), rfl⟩)

theorem exists_isFD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∃ F, IsFD (gammaU X hj κ) F := by
  intro E _ _ _ r j X hj Tau _ κ hp
  have := KU.countable_Γ X
  obtain ⟨hO, hD⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI Tau j (r - j)
  have hU : ∀ γ : X.Γ, toUpq X hj κ γ ∈ UpqI Tau j (r - j) := fun γ => gammaU_le X hj κ hp (Subgroup.mem_map_of_mem _ γ.2)
  have hmem : ∀ (γ : X.Γ), ∀ z ∈ DomI Tau j (r - j), moebI (toUpq X hj κ γ) z ∈ DomI Tau j (r - j) :=
    fun γ z hz t => moeb_mem (g := toUpq X hj κ γ t) (z := z t) (hU γ t trivial) (hz t)
  let a : X.Γ → DomFlat Tau j (r - j) → DomFlat Tau j (r - j) := fun γ v =>
    ⟨flat (moebI (toUpq X hj κ γ) (unflat v.1)), hmem γ _ v.2⟩
  have hx : ∀ v : DomFlat Tau j (r - j), ∃ x, IsOrth X x ∧ unflat v.1 = domPt X hj κ x := fun v => by
    obtain ⟨x, hx, e⟩ := GlobalTheory.TrueCx.FrameOnto.frame_onto E r j X hj Tau κ hp _ v.2
    obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
    exact ⟨x1, h1, by rw [← e, domPt_rmul X hj κ hb]⟩
  have hdom : ∀ {x}, IsOrth X x → x ∈ X.dom := fun h => KU.orth_dom X h
  have ha : ∀ (γ : X.Γ) v x, IsOrth X x → unflat v.1 = domPt X hj κ x →
      unflat (a γ v).1 = domPt X hj κ (lact γ x) := fun γ v x h e => by
    rw [domPt_lact X hj κ hp _ (hdom h), ← e]; rfl
  have hinj : ∀ v w : DomFlat Tau j (r - j), unflat v.1 = unflat w.1 → v = w := fun v w h =>
    Subtype.ext (congrArg flat h)
  have hcont : ∀ γ, Continuous (a γ) := fun γ => by
    have h : Continuous fun v : DomFlat Tau j (r - j) => flat (moebI (toUpq X hj κ γ) (unflat v.1)) :=
      continuousOn_iff_continuous_restrict.1 (hD _ (hU γ)).1.continuousOn
    exact h.subtype_mk _
  obtain ⟨F, hF, h1, h2⟩ := exists_section a hcont
    (fun γ δ v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, ha _ _ _ (KU.isOrth_lact X δ.2 h) (ha _ _ _ h e), KU.lact_lact]; rfl)
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      refine hinj _ _ ?_
      rw [ha _ _ _ h e, e, OneMemClass.coe_one, KU.lact_one])
    (fun v => by
      obtain ⟨x, h, e⟩ := hx v
      obtain ⟨W, hW, hf⟩ := eventually_finite X hj κ hp h v.2
      have hc : Continuous fun v : DomFlat Tau j (r - j) => unflat v.1 :=
        continuous_pi fun t => continuous_matrix fun a b => (continuous_apply (t, a, b)).comp continuous_subtype_val
      refine ⟨_, hc.continuousAt.preimage_mem_nhds hW, (hf.preimage Subtype.val_injective.injOn).subset ?_⟩
      intro γ hγ
      exact ⟨γ.2, by rw [← ha γ v x h e]; exact hγ⟩)
  refine ⟨Subtype.val '' F, (MeasurableEmbedding.subtype_coe hO.measurableSet).measurableSet_image.2 hF,
    Subtype.coe_image_subset _ _, fun z hz => ?_, ?_⟩
  · obtain ⟨γ, h⟩ := h1 ⟨flat z, hz⟩
    exact ⟨_, ⟨γ, γ.2, rfl⟩, _, h, rfl⟩
  · have he : {z | z ∈ Subtype.val '' F ∧ ∃ γ ∈ gammaU X hj κ,
        flat (moebI γ (unflat z)) ∈ Subtype.val '' F ∧ moebI γ (unflat z) ≠ unflat z} = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨v, hv, rfl⟩, _, ⟨γ, hγ, rfl⟩, ⟨w, hw, e⟩, hne⟩
      have e' : w = a ⟨γ, hγ⟩ v := Subtype.ext e
      exact hne (congrArg (fun v => unflat v.1) (h2 v hv ⟨γ, hγ⟩ (e' ▸ hw)))
    rw [he, measure_empty]

end GlobalTheory.BoundedFundDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoTies

set_option synthInstance.maxHeartbeats 400000 in
def BarAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (jf : T.cuspA j (wtA w) w.n → Hm.H) (Z : Prop) : Prop :=
  ¬ GoodEmb T.Q.c s → ∀ hV : T.V j ((starRingEnd ℂ).comp s) = W,
    ((∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) →
      ∃ v : M.Vec, IsUnitV v ∧ ∀ f, Hm.e (jf f) v = fun g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g)) ∧
    (¬ (∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) → Z)

theorem barTie_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) :
    BarTie t ↔ ∀ (i : Fin D.R.m) σ, BarAtOne T ((i : ℕ) + 1) (κ i) (res T σ) (R.MW i σ) (R.HW i σ) (fun f => t.jK i σ f) ((R.FW i).j σ = 0) :=
  Iff.rfl

theorem BarAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm)
    (jf : T.cuspA j (wtA w) w.n → Hm.H) (jf' : T'.cuspA j (wtA w') w'.n → Hm'.H)
    (hj : ∀ f f', HEq f' f → HEq (jf' f') (jf f)) {Z Z' : Prop} (hZ : Z → Z') :
    BarAtOne T j w s M Hm jf Z → BarAtOne T' j w' s' M' Hm' jf' Z' := by
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hj' : jf' = jf := funext fun f => eq_of_heq (hj f f HEq.rfl)
  subst hj'
  intro h hg hV
  exact ⟨(h hg hV).1, fun h' => hZ ((h hg hV).2 h')⟩

theorem reading_eq_zero {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hn : n = n')
    {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) (j' : (Fin n' → L') →ₛₗ[σ'] A')
    (h : ∀ x x', CrdOver ι x x' → HEq (j' x') (j x)) (h0 : j = 0) : j' = 0 := by
  subst hn
  subst h0
  have hz : HEq (j' 0) (0 : A) := h 0 0 ⟨rfl, fun k k' _ => (map_zero ι).symm⟩
  have hk : ∀ k, j' (Pi.single k 1) = 0 := fun k => by
    have h1 : HEq (j' (Pi.single k 1)) (0 : A) := h (Pi.single k 1) (Pi.single k 1) ⟨rfl, fun a b hab => by
      obtain rfl : a = b := Fin.ext hab
      by_cases hak : a = k
      · subst hak
        simp
      · simp [Pi.single_apply, hak]⟩
    exact (eq_of_heq (h1.trans hz.symm)).trans (map_zero j')
  refine LinearMap.ext fun x => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pi_eq_sum_univ' x, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smulₛₗ, hk, smul_zero]

theorem barTie_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        GeoTies.MWOver z.R.toRealDat R'.toRealDat → BarTie fw' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hMW
  letI := alg'
  letI := z.alg
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hE.1) :))
  refine (barTie_iff fw').2 fun i' σ' => ?_
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hE.2.2.2) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))
  have hb := (barTie_iff z.geo.fw).1 z.geo.bar i (σ'.comp ι)
  have hMM := hMW i i' hi ι hι σ'
  have hnW := hRS.1.2.2.2.2.2.1
  have hcl := ((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hj : ∀ φ φ', HEq φ' φ → HEq (fw'.jK i' σ' φ') (z.geo.fw.jK i (σ'.comp ι) φ) := fun φ φ' hφ =>
    hjj _ _ ⟨hn, fun k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hcrd i i' hi φ φ' hφ k k' hk).trans (hι _).symm)⟩
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (by with_unfolding_all exact (z.core.Q.H :)), l := (by with_unfolding_all exact (z.core.Q.l :)), c := (by with_unfolding_all exact (z.core.Q.c :)), Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let j₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → H₀.H := (by with_unfolding_all exact ((fun φ => z.geo.fw.jK i (σ'.comp ι) φ) :))
  exact BarAtOne.congr core₀ core' ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :))) ((by with_unfolding_all exact (c4 :))) ((by with_unfolding_all exact (c5 :))) ((by with_unfolding_all exact (c6 :))) ((by with_unfolding_all exact (c7 :))) ((by with_unfolding_all exact (c8 :))) ((by with_unfolding_all exact (c9 :))) ((by with_unfolding_all exact (c10 :)))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((by with_unfolding_all exact (hP :))) ((by with_unfolding_all exact (hM :))) ((by with_unfolding_all exact (hnn :))) s₀ (res core' σ') ((by with_unfolding_all exact (hs :))) M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :)))
    H₀ (R'.HW i' σ') ((by with_unfolding_all exact (hH :))) j₀ _ ((by with_unfolding_all exact (hj :))) hZ ((by with_unfolding_all exact (hb :)))

end GlobalTheory.Mem.R3.Rw.GeoTies
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) :
    LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S))) :=
  GlobalTheory.VVRank.pullTo σ (snd (Over.mk (𝟙 S)) G).left (fun _ => Category.comp_id _)

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecOfMulToMatMul
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
open scoped Kronecker

namespace GlobalTheory.FlagFibre

theorem vecOf_mul_toMat_mul {p q : ℕ} (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ)
    (v : Fin p × Fin q → ℂ) : Formalism.MJ.vecOf (R * toMat v * T) = Matrix.toLin' (R ⊗ₖ Tᵀ) v := by
  funext ⟨a, b⟩
  simp only [Formalism.MJ.vecOf, Matrix.toLin'_apply, mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    kroneckerMap_apply, transpose_apply, toMat, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem lintegral_affine :
    ∀ (p q : ℕ) (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ), IsUnit R.det → IsUnit T.det → ∀ f : (Fin p × Fin q → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ v : Fin p × Fin q → ℂ, f (vecOf (R * toMat v * T + C)) = ENNReal.ofReal ((Complex.normSq R.det ^ q * Complex.normSq T.det ^ p)⁻¹) * ∫⁻ v, f v := by
  intro p q R T C hR hT f hf
  set Lr : (Fin p × Fin q → ℂ) →ₗ[ℝ] (Fin p × Fin q → ℂ) := (Matrix.toLin' (R ⊗ₖ Tᵀ)).restrictScalars ℝ with hLr
  have hdet : LinearMap.det Lr = Complex.normSq R.det ^ q * Complex.normSq T.det ^ p := by
    rw [hLr, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin', det_kronecker,
      det_transpose]
    simp
  have hpos : 0 < Complex.normSq R.det ^ q * Complex.normSq T.det ^ p :=
    mul_pos (pow_pos (Complex.normSq_pos.2 hR.ne_zero) _) (pow_pos (Complex.normSq_pos.2 hT.ne_zero) _)
  have hdet0 : LinearMap.det Lr ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hLm : Measurable Lr := (LinearMap.continuous_of_finiteDimensional Lr).measurable
  have hg : Measurable fun w : Fin p × Fin q → ℂ => f (w + Formalism.MJ.vecOf C) := hf.comp (measurable_add_const _)
  have e1 : ∫⁻ v : Fin p × Fin q → ℂ, f (Formalism.MJ.vecOf (R * toMat v * T + C)) =
      ∫⁻ w, f (w + Formalism.MJ.vecOf C) ∂(Measure.map Lr volume) := by
    rw [lintegral_map hg hLm]
    refine lintegral_congr fun v => ?_
    have : Formalism.MJ.vecOf (R * toMat v * T + C) = Formalism.MJ.vecOf (R * toMat v * T) + Formalism.MJ.vecOf C := rfl
    rw [this, vecOf_mul_toMat_mul]; rfl
  refine e1.trans ?_
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet0, lintegral_smul_measure, hdet,
    abs_of_nonneg (inv_nonneg.2 hpos.le), smul_eq_mul, lintegral_add_right_eq_self]

end GlobalTheory.FlagFibre
end

