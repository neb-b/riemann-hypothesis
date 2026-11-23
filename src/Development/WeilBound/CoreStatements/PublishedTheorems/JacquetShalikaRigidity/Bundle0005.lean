module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LApply
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKY

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def I (ν : Measure (GA E k)) [IsFiniteMeasure ν] : XB E k →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ g, f g ∂ν
      map_add' := fun f f' => integral_add (f.integrable ν) (f'.integrable ν)
      map_smul' := fun c f => integral_smul c (fun g => f g) }
    (ν.real Set.univ) (fun f => f.norm_integral_le_mul_norm ν)

def L (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' : XB E k) (h : GA E k) : XB E k →L[ℂ] ℂ :=
  (I ν).comp (((ContinuousLinearMap.mul ℂ (XB E k)).flip (star φ')).comp (Rt E k h))

theorem L_apply (ν : Measure (GA E k)) [IsFiniteMeasure ν] (φ' x : XB E k) (h : GA E k) :
    L ν φ' h x = ∫ g, x (g * h) * conj (φ' g) ∂ν := by
  first
    | rfl
    | (simp only [L, I, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.mul_apply', LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
        BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.star_apply]
       rfl)

end PKY

theorem ky_of : W0 → KY := by
  intro hW E _ _ _ k μ _ hk β hβ φ'
  have hfin : (μ.withDensity β) (band E k) < ⊤ := (hW E k μ hk).2 β hβ
  haveI hνf : IsFiniteMeasure ((μ.withDensity β).restrict (band E k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hLR : ∀ (h a : GlobalTheory.CuspRep.GA E k) (x : PositivityTheory.jumpWindows.XB E k),
      PKY.L ((μ.withDensity β).restrict (band E k)) φ' h (PositivityTheory.jumpWindows.Rt E k a x) =
        PKY.L ((μ.withDensity β).restrict (band E k)) φ' (h * a) x := by
    intro h a x
    show PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ'))
        (PositivityTheory.jumpWindows.Rt E k h (PositivityTheory.jumpWindows.Rt E k a x))) =
      PKY.I _ (((ContinuousLinearMap.mul ℂ (PositivityTheory.jumpWindows.XB E k)).flip (star φ')) (PositivityTheory.jumpWindows.Rt E k (h * a) x))
    rw [map_mul]
    rfl
  let Y : Submodule ℂ (PositivityTheory.jumpWindows.XB E k) :=
    { carrier := {x | (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
          ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0}
      add_mem' := by
        rintro x x' ⟨hx1, hx2⟩ ⟨hx1', hx2'⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g) + x' (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g + x' g
          rw [hx1, hx1']
        · rw [map_add (f := _), hx2, hx2', add_zero]
      zero_mem' := ⟨fun t g => rfl, fun h => map_zero _⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2⟩
        refine ⟨fun t g => ?_, fun h => ?_⟩
        · show c • x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = c • x g
          rw [hx1]
        · rw [map_smul, hx2, smul_zero] }
  have hmemL : ∀ x, x ∈ Y ↔ (∀ (t : ℝ) (g : GlobalTheory.CuspRep.GA E k), x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g) ∧
      ∀ h, PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0 := fun x => Iff.rfl
  have hc : IsClosed (Y : Set (PositivityTheory.jumpWindows.XB E k)) := by
    have hset : (Y : Set (PositivityTheory.jumpWindows.XB E k)) =
        (⋂ (t : ℝ), ⋂ (g : GlobalTheory.CuspRep.GA E k),
          {x : PositivityTheory.jumpWindows.XB E k | x (GlobalTheory.UnitaryBC.splitCentre E k t * g) = x g}) ∩
        ⋂ h, {x : PositivityTheory.jumpWindows.XB E k | PKY.L ((μ.withDensity β).restrict (band E k)) φ' h x = 0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact hmemL x
    rw [hset]
    exact (isClosed_iInter fun t => isClosed_iInter fun g =>
        isClosed_eq (BoundedContinuousFunction.evalCLM ℂ (GlobalTheory.UnitaryBC.splitCentre E k t * g)).continuous
          (BoundedContinuousFunction.evalCLM ℂ g).continuous).inter
      (isClosed_iInter fun h => isClosed_eq (PKY.L _ φ' h).continuous continuous_const)
  refine ⟨Y, hc, ?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨hx1, hx2⟩ := (hmemL x).mp hx
    refine (hmemL _).mpr ⟨fun t g => ?_, fun h => ?_⟩
    · show x (GlobalTheory.UnitaryBC.splitCentre E k t * g * a) = x (g * a)
      rw [mul_assoc, hx1]
    · rw [hLR]
      exact hx2 _
  · intro x
    rw [hmemL]
    exact and_congr Iff.rfl (forall_congr' fun h => by rw [PKY.L_apply])
  · intro φ hφ ψ S U η s hcut
    have hφ2 := ((hmemL φ).mp hφ).2
    let F : (Fin k → GlobalTheory.CuspRep.Ad E) → PositivityTheory.jumpWindows.XB E k := fun y => (η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ
    have hFc : Continuous F := hcut.contV
    have hFs : HasCompactSupport F := by
      have h1 : HasCompactSupport (fun y => (η y : ℂ)) :=
        hcut.cpt.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
      exact h1.smul_right (f' := fun y => PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ)
    have hFi : Integrable F (GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) :=
      hFc.integrable_of_hasCompactSupport hFs
    have hpt : ∀ g : GlobalTheory.CuspRep.GA E k,
        (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) =
          (∫ y, F y ∂GroundTheory.Automorphic.FourierWhittaker.vecMeasure E (Fin k)) (g * 1) := by
      intro g
      rw [mul_one]
      exact (BoundedContinuousFunction.evalCLM ℂ g).integral_comp_comm hFi
    simp_rw [hpt]
    rw [← PKY.L_apply, ← ContinuousLinearMap.integral_comp_comm _ hFi]
    have hz : ∀ y, PKY.L ((μ.withDensity β).restrict (band E k)) φ' 1 (F y) = 0 := fun y => by
      show PKY.L _ φ' 1 ((η y : ℂ) • PositivityTheory.jumpWindows.Rt E k (s y)⁻¹ φ) = 0
      rw [map_smul, hLR, one_mul, hφ2, smul_zero]
    simp only [hz, integral_zero]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LastRowIntegral
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LastRowIntegral

open ValuativeRel

theorem mul_apply_last {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (hi : (i : ℕ) + 1 = n) (h0 : ∀ j, j < i → A i j = 0) (h1 : A i i = 1) (c : Fin n) : (A * B) i c = B i c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [h1, one_mul]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h0 j h, zero_mul]
    · exfalso
      have h2 := j.isLt
      have h3 : (i : ℕ) < j := h
      omega
  · intro h; exact absurd (Finset.mem_univ i) h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_eq {k : ℕ} (hk : 1 ≤ k) (g : GA E k) (c : Fin k) :
    lastRow g c = g.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp only; omega)]
  · intro j _ hj
    rw [if_neg]
    intro h; apply hj; ext; simp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lastRow_UU {k : ℕ} (hk : 1 ≤ k) {n : GA E k} (hn : UU 0 n) (g : GA E k) :
    lastRow (n * g) = lastRow g := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul]
  refine mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hn.1 _ _ hj) (hn.2.1 _) c

theorem continuous_lastRow {k : ℕ} : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Units.continuous_val.matrix_elem i c
  · exact continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

theorem mem_int (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ 𝒪[w.adicCompletion E]) :
    x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  rw [hO] at hx
  exact hx

end LastRowIntegral

namespace LastRowIntegral

open ValuativeRel GroundTheory.Automorphic.Iwasawa

theorem last_int {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) (ιw : GL (Fin k) F →* GL (Fin m) F)
    (hu : ∀ n ∈ unipotent F k, ιw n ∈ unipotent F m)
    (hκ : ∀ κ ∈ GLnLocal.integralGL F k, ιw κ ∈ GLnLocal.integralGL F m)
    (ht : ∀ l, ιw (torusPow F k l) = torusPow F m (pad m l)) (h : GL (Fin k) F)
    (ha : Antitone (iwasawaExponent F m (ιw h))) (c : Fin k) : h ⟨k - 1, by omega⟩ c ∈ 𝒪[F] := by
  obtain ⟨u, hu0, κ, hκ0, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F k h
  set l := iwasawaExponent F k h
  have hl : iwasawaExponent F m (ιw h) = pad m l := by
    rw [he, map_mul, map_mul, ht]
    exact iwasawaExponent_eq F m (hu u hu0) (hκ κ hκ0)
  rw [hl] at ha
  have h0 : 0 ≤ l ⟨k - 1, by omega⟩ := by
    have := ha (show (⟨k - 1, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.2 (by omega))
    simpa [pad, show k - 1 < k by omega] using this
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le h0
  rw [he, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hu0.1 hj) (hu0.2 _) c, coe_torusPow,
    Matrix.diagonal_mul, he', zpow_natCast]
  exact Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _)
    (((GLnLocal.mem_integralGL_iff F k).1 hκ0).1 _ _)

end LastRowIntegral

theorem last_row_integral_of : jumpWindows.G0 → CornerEmbedding → K8 → K6 := by
  intro hG0 h5 h8 E _ _ _ m k hk hkm ψ hψ S hS ι hι α M U φ hP
  obtain ⟨hex, hι5⟩ := h5 E m k hkm.le
  obtain ⟨-, hblk, hsurj, -, -, hcpt, -, hloc, hcInf, hUU, -⟩ := hι5 ι hι
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg0, -, -, -, -⟩ := hG0 E k
  obtain ⟨-, -, hW⟩ := h8 E m ψ hψ S hS α φ hP.good hP.sat
  obtain ⟨C, -, hCblk, hCcpt, -, -, hB⟩ := hP.bump
  choose ιw hιw using fun w : Pl E => hex (w.adicCompletion E)
  have hlw := fun w => hloc w (ιw w) (hιw w)
  refine ⟨(fun p => p.1 + p.2) '' ((lastRow '' (ι ⁻¹' C)) ×ˢ
    Set.pi Set.univ (fun _ => sFin E '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))), ?_, ?_⟩
  · exact (((hcpt C hCcpt).image LastRowIntegral.continuous_lastRow).prod (isCompact_univ_pi fun _ =>
      (GroundTheory.Global.isCompact_integralFiniteAdeles E).image LastRowIntegral.continuous_sFin)).image
      (continuous_fst.add continuous_snd)
  intro g hg
  obtain ⟨hW1, hW2⟩ := hW (ι g) hg
  obtain ⟨g₀, h0i, h0S, h0in⟩ := hg0 S g
  have hinf : cInf (ι g₀) = cInf (ι g) := by
    have e : g = g₀ * (g₀⁻¹ * g) := by group
    have h1 : cInf (g₀⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0i, inv_mul_cancel]
    conv_rhs => rw [e, map_mul, map_mul, hcInf _ h1, mul_one]
  have hSl : ∀ w ∈ S, cLoc w (ι g₀) = cLoc w (ι g) := fun w hw => by
    rw [(hlw w).2.1, (hlw w).2.1, h0S w hw]
  have hin : InS S (ι g₀) := fun w hw => by rw [(hlw w).2.1, h0in w hw, map_one]
  have hne := hW1 (ι g₀) hinf hSl hin
  have hmir : Mir k (ι g₀) := fun i c h => hblk g₀ i c (h.imp id Nat.le_of_lt)
  obtain ⟨n, c, hc, t, hn, -, heq, -, -⟩ := hB (ι g₀) ⟨hin, hmir⟩ hne
  obtain ⟨c', rfl⟩ := hsurj c (hCblk c hc)
  have hn' : n = ι (g₀ * c'⁻¹) := by rw [map_mul, map_inv, heq, mul_inv_cancel_right]
  have hU0 : UU 0 (g₀ * c'⁻¹) := (hUU _).1 (hn' ▸ hn)
  have hA : lastRow g₀ = lastRow c' := by
    conv_lhs => rw [show g₀ = (g₀ * c'⁻¹) * c' by group]
    exact LastRowIntegral.lastRow_UU hk hU0 c'
  refine ⟨(lastRow g₀, lastRow g - lastRow g₀), ⟨⟨c', hc, hA.symm⟩, fun i _ => ?_⟩, by simp⟩
  refine ⟨pFin E ((lastRow g - lastRow g₀) i), ?_, ?_⟩
  · intro v
    change pLoc E v (pFin E ((lastRow g - lastRow g₀) i)) ∈ v.adicCompletionIntegers E
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub, map_sub]
    change (cLoc v g).val _ i - (cLoc v g₀).val _ i ∈ v.adicCompletionIntegers E
    by_cases hv : v ∈ S
    · rw [h0S v hv, sub_self]; exact zero_mem _
    · rw [h0in v hv]
      refine sub_mem (LastRowIntegral.mem_int v _ ?_) (LastRowIntegral.mem_int v _ ?_)
      · have ha := hW2 v hv
        rw [(hlw v).2.1] at ha
        exact LastRowIntegral.last_int hk hkm (ιw v) (hlw v).2.2.1 (hlw v).2.2.2.1 (hlw v).2.2.2.2 _ ha i
      · change (1 : Matrix (Fin k) (Fin k) (v.adicCompletion E)) _ i ∈ _
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
  · refine ad_ext ?_ rfl
    change (infEq E).symm 0 = _
    rw [map_zero]
    change (0 : Cinf E) = pInf E ((lastRow g - lastRow g₀) i)
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub]
    change (0 : Cinf E) = (cInf g).val _ i - (cInf g₀).val _ i
    rw [h0i, sub_self]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LevelScalarAction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LevelScalarAction

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lev_smul {S : Finset (Pl E)} {x : XB E k} (h : Lev S x) (c : ℂ) : Lev S (c • x) := by
  intro w hw
  filter_upwards [h w hw] with u hu
  have hu' : repW k w u x = x := hu
  change repW k w u (c • x) = c • x
  rw [map_smul, hu']

end LevelScalarAction

theorem global_level_of : jumpWindows.G0 → jumpWindows.G1 → jumpWindows.AlmostEverywhereSpherical → jumpWindows.G2c → jumpWindows.G5 → K8 → K9 := by
  intro hG0 hG1 hG1b hG2c hG5 hK8 E _ _ _ k _ ψ hψ hcond π hπ
  obtain ⟨φ₀, hφ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨x₀, hx₀, -, hlev⟩ := hG1 E k π hπ φ₀ hφ₀
  have hev := hcond.and (hG1b E k π hπ φ₀ hφ₀ x₀ hx₀)
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, fun S hS => ?_⟩
  have hoff : ∀ w, w ∉ S → Cond ψ w ∧ ∀ B, (CG.mk π).HasSat w B → SatFn w B x₀ := by
    intro w hw
    by_contra hc
    exact hw (hS ((Set.Finite.mem_toFinset _).2 hc))
  refine ⟨fun w hw => (hoff w hw).1, fun α hα => ?_⟩
  have hgood : Good ψ (k - 1) (x₀ : GA E k → ℂ) := by
    rw [hx₀]; exact _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E k ψ φ₀ (π.cusp _ hφ₀)
  have hx0 : x₀ ≠ 0 := by
    intro h
    subst h
    exact hne (Subtype.ext (by rw [← hx₀]; rfl))
  obtain ⟨g, hg⟩ := ((hG5 E k ψ hψ).2.2.2 x₀ hgood).2.1 hx0
  have hsat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) x₀ := fun w => (hoff w.1 w.2).2 _ (hα w)
  obtain ⟨g₀, h1, h2, h3⟩ := (hG0 E k).2.2.2.2.2.2.2.2.2.2.1 S g
  have hne0 : Wh ψ x₀ g₀ ≠ 0 :=
    ((hK8 E k ψ hψ S (fun w hw => (hoff w hw).1) α x₀ hgood hsat).2.2 g hg).1 g₀ h1 h2 h3
  refine ⟨(Wh ψ x₀ g₀)⁻¹ • φ₀, π.V.smul_mem _ hφ₀, g₀, (Wh ψ x₀ g₀)⁻¹ • x₀, h3, ?_, ?_, LevelScalarAction.lev_smul (hlev S) _, ?_⟩
  · funext y
    change (Wh ψ x₀ g₀)⁻¹ * x₀ y = (Wh ψ x₀ g₀)⁻¹ * φ₀.1 y
    rw [hx₀]
  · intro w
    obtain ⟨Y, -, -, hY⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hY _).1 (Y.smul_mem _ ((hY x₀).2 (hsat w)))
  · rw [(hG5 E k ψ hψ).2.1, one_mul]
    change whit ψ (k - 1) (fun y => (Wh ψ x₀ g₀)⁻¹ * x₀ y) g₀ = 1
    rw [GlobalTheory.CuspRep.Generic.whit_smul]
    exact inv_mul_cancel₀ hne0

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalUnramifiedOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w (n := a), Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w (n := a),
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w (n := a))
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
end

