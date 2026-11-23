module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsScalarPreservesIntegralMatricesSubst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section
namespace GlobalTheory.LocOm

theorem exists_integral_multiplier {k : Type} [Field k] [ValuativeRel k] (a : k) :
    ∃ b : k, b ≠ 0 ∧ b ∈ 𝒪[k] ∧ b * a ∈ 𝒪[k] := by
  by_cases ha : a ∈ 𝒪[k]
  · exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by rintro rfl; exact ha (Subring.zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero ha0, ?_, by simp [ha0, Subring.one_mem]⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    push_neg at ha
    exact inv_le_one_of_one_le₀ ha.le

theorem exists_common_integral_multiplier {k : Type} [Field k] [ValuativeRel k]
    {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ c : k, c ≠ 0 ∧ c ∈ 𝒪[k] ∧ ∀ i, c * f i ∈ 𝒪[k] := by
  classical
  choose b hb0 hbO hbf using fun i => exists_integral_multiplier (f i)
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr fun i _ => hb0 i,
    Subring.prod_mem _ fun i _ => hbO i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i), mul_comm (b i), mul_assoc]
  exact Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hbO j) (hbf i)

theorem enl_scalar_denominator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), ∃ c : kˣ, ∀ zk : GL Y k, (zk : Matrix Y Y k) = (c : k) • (1 : Matrix Y Y k) → Enl gk (hk * zk⁻¹) ∧ Enl (1 : GL Y' k) zk⁻¹ := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk
  obtain ⟨c, hc0, hcO, hc⟩ := exists_common_integral_multiplier
    (fun p : Y × Y × Y' × Y' => (↑(hk⁻¹) : Matrix Y Y k) p.1 p.2.1 * (↑gk : Matrix Y' Y' k) p.2.2.1 p.2.2.2)
  refine ⟨Units.mk0 c hc0, fun zk hz => ⟨?_, ?_⟩⟩
  · intro x hx r q
    have : ((↑((hk * zk⁻¹)⁻¹) : Matrix Y Y k)) = c • (↑(hk⁻¹) : Matrix Y Y k) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hz]
      simp
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    have h1 := hc (r, s, t, q)
    have h2 := hx s t
    simp only at h1
    have : c * ((↑(hk⁻¹) : Matrix Y Y k) r s * x s t * (↑gk : Matrix Y' Y' k) t q) =
      (c * ((↑(hk⁻¹) : Matrix Y Y k) r s * (↑gk : Matrix Y' Y' k) t q)) * x s t := by ring
    rw [this]
    exact Subring.mul_mem _ h1 h2
  · intro x hx r q
    rw [inv_inv, hz]
    simp only [Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul, Units.val_mk0]
    exact Subring.mul_mem _ hcO (hx r q)

end GlobalTheory.LocOm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def place (q : SplitPt D k) : GlobalTheory.LocMod.Place D k where
  e := q.e
  split := q.split
  π := q.pr
  ι := q.sec
  π_ι := q.pr_sec
  ι_π := q.sec_pr
  cont_π := q.cont_pr
  cont_ι := q.cont_sec

theorem suppAt_one (e : AE D) (S : HSp D) : SuppAt e S 1 := by
  intro i j
  simp [Formalism.L2.Theta.mt]

theorem isLoc_one (q : SplitPt D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : (place q).IsLoc F 1 1 := by
  refine ⟨suppAt_one _ _, ?_⟩
  simp [Formalism.L2.Theta.mt, F.βγ, place]

theorem locGrp (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    (∀ gk : GL Y k, ∃! g, (place q).IsLoc F g gk) ∧ (∀ g, SuppAt (place q).e S g → ∃ gk, (place q).IsLoc F g gk) ∧
      ∀ g gk h hk, (place q).IsLoc F g gk → (place q).IsLoc F h hk → (place q).IsLoc F (g * h) (gk * hk) :=
  (_root_.GlobalTheory.LocGrp.local_groups D k (place q)).1 S Y F

def frameOf (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : Frame q S Y where
  b := F.β
  b' := F.γ
  bb' := F.βγ
  b'b := F.γβ
  gl :=
    { toFun := fun g => ((locGrp q S Y F).1 g).exists.choose
      map_one' := ((locGrp q S Y F).1 1).unique ((locGrp q S Y F).1 1).exists.choose_spec (isLoc_one q F)
      map_mul' := fun g g' => ((locGrp q S Y F).1 (g * g')).unique ((locGrp q S Y F).1 (g * g')).exists.choose_spec
        ((locGrp q S Y F).2.2 _ _ _ _ ((locGrp q S Y F).1 g).exists.choose_spec
          ((locGrp q S Y F).1 g').exists.choose_spec) }
  gl_supp g := ((locGrp q S Y F).1 g).exists.choose_spec.1
  gl_mat g := ((locGrp q S Y F).1 g).exists.choose_spec.2

def stdLat (k : Type) [Field k] [ValuativeRel k] (Y : Type) : Submodule 𝒪[k] (Y → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

theorem mem_std {Y : Type} (y : Y → k) : y ∈ stdLat k Y ↔ ∀ i, y i ∈ 𝒪[k] := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨y i, h⟩, rfl⟩⟩

theorem std_eq_span (Y : Type) [Fintype Y] [DecidableEq Y] :
    stdLat k Y = Submodule.span 𝒪[k] (Set.range fun i : Y => (Pi.single i 1 : Y → k)) := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_std x).1 hx
    have : x = ∑ i, (⟨x i, hx' i⟩ : 𝒪[k]) • (Pi.single i 1 : Y → k) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine (mem_std _).2 fun i => ?_
    show (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k]
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem isLattice_std (Y : Type) [Fintype Y] [DecidableEq Y] : Submodule.IsFullLattice k (stdLat k Y) := by
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · apply Submodule.IsLattice.of_fg k
    rw [std_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · apply eq_top_iff.mpr
    rw [← (Pi.basisFun k Y).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine (mem_std _).2 fun j => ?_
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((_root_.GlobalTheory.FinPl.localComponents D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem exists_selfDual_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (L₀ : Lat S), IsSelfDualC S L₀ → ∃ L : Lat S, IsSelfDualC S L ∧ (∀ v, v ≠ q.v → latV S L (· = v) = latV S L₀ (· = v)) ∧ ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  intro D k _ _ _ _ q S Y _ _ F L₀ hL₀
  obtain ⟨M, hM, hMΛ, hoff⟩ :=
    _root_.GlobalTheory.FrameGlob.main D k q S Y (frameOf q S Y F) L₀ (stdLat k Y) hL₀ (isLattice_std Y)
  refine ⟨M, hM, fun v hv => le_antisymm (latV_le_of_off hM.1 hL₀.1 hv hoff)
    (latV_le_of_off hL₀.1 hM.1 hv hoff.symm), fun y => ?_⟩
  exact (mem_std y).symm.trans (hMΛ y)

end GlobalTheory.SplitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualOrthAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSumLat

variable {D : D7}

theorem rat_mulVec_mem_latV {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem dsum_eq' {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA' {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

theorem exists_selfDual_orthAt : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B), IsSelfDualC A LA →
    IsSelfDualC B LB → ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  intro D S A B o LA LB hA hB
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨Submodule.IsLattice.of_fg D.host.E ((hA.1.fg.map _).sup (hB.1.fg.map _)), fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq'] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
    rw [star_add, add_dotProduct, pair_iA', e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq', pair_iA', ← dsum_eq'] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
      rwa [dsum_eq', e2, ← dsum_eq'] at this
  · have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
        change (o.iA.map (incA D)) * (o.qA.map (incA D)) + (o.iB.map (incA D)) * (o.qB.map (incA D)) = 1
        rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add (incA D)), o.iA_qA_add, Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))]
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, hs, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem_latV _ hiA h.1) (rat_mulVec_mem_latV _ hiB h.2)

end GlobalTheory.OrthSumLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLocalSupportedScalarComponent
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocScalar

theorem place_ι_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have hx : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]
  have := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at this
  rw [this, ← mul_assoc, hx]

theorem place_ι_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have := p.ι_π 1
  rwa [map_one, mul_one] at this

theorem place_π_e {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  rw [← place_ι_one, p.π_ι]

theorem exists_isLoc_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  intro D k _ _ _ _ p V Z _ _ F c zk hzk
  have he := p.split
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv V)
    (GlobalTheory.SplitOnto.gram_conj V) he.1 he.2.1 (p.ι (c : k) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (p.ι ((c⁻¹ : kˣ) : k) • 1) (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul (p.ι _), ← place_ι_mul, Units.inv_mul, place_ι_one, smul_smul, he.1])
  let z : GA D V := ⟨g, h1⟩
  refine ⟨z, fun i j => congrFun (congrFun h2 i) j, ?_⟩
  rw [hzk, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, F.βγ]
  ext i j
  have := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  change p.π (g.1 i j) = _
  rw [← one_mul (p.π (g.1 i j)), ← place_π_e p, ← map_mul, this, map_mul, place_π_e, one_mul]
  by_cases hij : i = j
  · subst hij; simp [p.π_ι]
  · simp [hij]

end GlobalTheory.LocScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExpTraceEqBrk
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceBrk

theorem exp_trace_eq_brk : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ M Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y) : ℚ) : ℂ)) = brk (HV sc) (embH (tauE D) δ (Matrix.toLin' Y)) (embH (tauE D) δ (Matrix.toLin' M)) := by
  intro D ψ θ S T δ sc h M Y
  have hz : ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) τ i j,
      embH (tauE D) δ (Matrix.toLin' γ) τ i j = δ * tauE D τ (γ i j) := by
    intro γ τ i j
    simp [embH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hδ : δ * starRingEnd ℂ δ = ((‖δ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hHV : HV sc (embH (tauE D) δ (Matrix.toLin' M)) (embH (tauE D) δ (Matrix.toLin' Y)) =
      ((sc * ‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M Y) := by
    rw [GlobalTheory.LatSign.hRat_one S T h.gS h.gT]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HV, LinearMap.mk₂'ₛₗ_apply, hz, map_sum, map_mul, GlobalTheory.LatSign.tauE_star']
    rw [Complex.ofReal_mul, ← hδ, mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [brk, Formalism.L2.Th1.H.altE, hHV, h.scale, ← GlobalTheory.LatSign.sum_two_re_eq_trace, Complex.im_ofReal_mul,
    Complex.im_sum, ← Complex.ofReal_sum]
  have hs : ∑ τ, 2 * (tauE D τ (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y)).re =
      -(2 * (Real.sqrt D.host.d)⁻¹ * ∑ τ, (tauE D τ (GlobalTheory.LatVac.hRat S T M Y)).im) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, h.xi, mul_assoc, Complex.I_mul_re, Complex.im_ofReal_mul]
    ring
  rw [hs, Complex.ofReal_neg]
  congr 1
  ring

end GlobalTheory.TraceBrk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFourierJacobiToBesselColumnMulLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatColLawFB

open GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frame_col (p : Place D k) {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (hB : p.IsBesFrame B (s * p.xi) FA FV)
    (j : Fin (σ + 1)) (l : Fin c) (hl : l.val = j.val) (x : Fin B.V.rank) :
    FV.β x (Sum.inr l) = s * p.xi ^ (σ + 1 - j.val) * ((xLast B.d (vecB B.o B.ζ)).map p.π) x j := by
  obtain ⟨-, -, hX, hz, -⟩ := hB
  induction j using Fin.lastCases with
  | last =>
    rw [hz l hl x]
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last, Fin.val_last, Nat.add_sub_cancel_left, pow_one]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  | cast j =>
    rw [hX j l hl x]
    have hj := j.isLt
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc, Fin.val_castSucc]
    rw [show σ + 1 - j.val = (σ - j.val) + 1 by omega, pow_succ', ← mul_assoc]
    rfl

theorem flatFB_mulcol : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ σ ∧ ¬ Free (σ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hjac _ hbes Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * σ + 1 := hbes.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin (σ + 1) := ⟨i.val, by omega⟩
  let zk : Matrix (Fin (σ + 1)) (Fin B.V.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (σ + 1 - i.val)) * FV.γ r β else 0
  let a : Mx D B.V.rank (σ + 1) := giA B.V * adj (zk.map p.ι : Mx D (σ + 1) B.V.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (J.d.extY B.V a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin (σ + 1), (FV.γ * (xLast B.d (vecB B.o B.ζ)).map p.π) r j = (s * p.xi ^ (σ + 1 - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FV.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (frame_col p B s FA FV hbes j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO J.W B.V (p.up FW FV t) (J.d.extY B.V a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FV.γβ, Matrix.one_mul,
      col_mul _ _ FW.β i₀ (Sum.inr i) (hκ _) (hjac.2.2.1 i₀ i rfl), Matrix.mul_assoc, FW.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO J.W B.V (J.d.extX B.V (xLast B.d (vecB B.o B.ζ))) (J.d.extY B.V a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv B.V (xLast B.d (vecB B.o B.ζ)) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).2 σ J B st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatFB_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLawFB

end
end

